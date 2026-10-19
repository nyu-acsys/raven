open Base
open Ast
open Util
open Smt
module Session = SmtSolver.SmtSession

type focus = { extents : Loc.t list; assertion : string option }
(** What `--only` selects: the procedures declared within the [extents], and in them only
    the [assertion] of that name, if any. *)

type fingerprinting = {
  run_key : string;  (** What the run fixes: the build of Raven, and the solver. *)
  symbol_text : Module.symbol -> string;
  report : bool;  (** Whether the fingerprints are output. *)
}
(** How the proof obligations' fingerprints are computed (see [Fingerprints]). *)

type context = {
  session : SmtSolver.session;
  path_conditions : expr list;
  auto_dependencies : Dependencies.Graph.t;
  diagnostics : Diagnostics.t;  (** The run's, for the verification errors. *)
  focus : focus option;
  counterexamples : bool;  (** Whether failed checks report a counterexample. *)
  fingerprinting : fingerprinting option;
  cache : VerificationCache.t option;
  fingerprints : string qual_ident_map;  (** Those of the obligations, when computed. *)
  used_fingerprints : string list;
      (** The fingerprints of the obligations found in the cache or verified. *)
  failed : bool;  (** Whether a check of the procedure being checked failed. *)
  on_scheduled : (Diagnostics.MemberStatus.procedure list -> unit) option;
      (** Gets the procedures and named assertions still to be checked, once it is known
          which are. *)
  heap_fields : (string, string) Hashtbl.t;
      (** The field each field's heap variable is named after, by the heap's name. *)
  sequence_functions : type_expr -> (qual_ident * qual_ident) option;
      (** The [length] and [index] functions of a type that has them, like a sequence. *)
  branches : Counterexample.branch list;
      (** The conditionals entered in the procedure being checked, latest first. *)
  arms : (int * bool) list;
      (** The arms of the conditionals the current statement is in, innermost first. *)
  next_branch : int;
}

type 'a t = context -> context * 'a

let create ?focus ?(counterexamples = false) ?fingerprinting ?cache ?on_scheduled
    ~diagnostics session =
  {
    session;
    path_conditions = [];
    auto_dependencies = Dependencies.Graph.empty;
    diagnostics;
    focus;
    counterexamples;
    fingerprinting;
    cache;
    fingerprints = Map.empty (module QualIdent);
    used_fingerprints = [];
    failed = false;
    on_scheduled;
    heap_fields = Hashtbl.create (module String);
    sequence_functions = (fun _ -> None);
    branches = [];
    arms = [];
    next_branch = 0;
  }

(** Forgets the conditionals of the procedure checked before. *)
let start_procedure : unit t =
 fun context -> ({ context with branches = []; arms = []; failed = false }, ())

(** Records entering the conditional at [loc] with the test [test], and returns its id. *)
let enter_branch ~(loc : Loc.t) (test : expr) : int t =
 fun context ->
  let id = context.next_branch in
  let branch = { Counterexample.id; stmt_loc = loc; test; arm = List.hd context.arms } in
  ({ context with branches = branch :: context.branches; next_branch = id + 1 }, id)

(** Runs [m] in the arm of the conditional [id], the [then] arm if [arm]. *)
let in_arm id arm (m : 'a t) : 'a t =
 fun context ->
  let context', a = m { context with arms = (id, arm) :: context.arms } in
  ({ context' with arms = context.arms }, a)

(** Whether the procedure declared at [loc] is checked. *)
let in_focus (loc : Loc.t) : bool t =
 fun context ->
  ( context,
    match context.focus with
    | None -> true
    | Some focus ->
        List.exists focus.extents ~f:(fun extent ->
            Diagnostics.MemberStatus.contains extent loc) )

(** Whether the assertion named [name], if it is named, is checked; [None] if every
    assertion is. *)
let focused_assertion : string option t =
 fun context -> (context, Option.bind context.focus ~f:(fun focus -> focus.assertion))

(** Records the verification error [diag]. Aborts when it is one more than the limit, or
    when the solver was stopped, since nothing more can be checked. *)
let record_error (diag : Error.t list) : unit t =
 fun context ->
  Diagnostics.record_error context.diagnostics diag;
  if context.diagnostics.aborted || Session.is_closed context.session then
    Error.fail_with (Diagnostics.report_errors context.diagnostics)
  else (context, ())

(** Records the [outcome] of checking the procedure [proc]. *)
let record_result (proc : Diagnostics.MemberStatus.procedure)
    (outcome : Diagnostics.MemberStatus.outcome) : unit t =
 fun context ->
  Diagnostics.record_result context.diagnostics proc outcome;
  let failed =
    match outcome with
    | Failed | Timeout -> true
    | Cached | Verified | Pending -> context.failed
  in
  ({ context with failed }, ())

(** The fingerprint of the obligation [qual_name], if fingerprints are computed, and
    whether the cache has it. *)
let fingerprint qual_name : (string * bool) option t =
 fun context ->
  ( context,
    Option.map (Map.find context.fingerprints qual_name) ~f:(fun fingerprint ->
        ( fingerprint,
          Option.exists context.cache ~f:(fun cache ->
              VerificationCache.mem cache fingerprint) )) )

(** Notes that the obligation of [fingerprint] was found in the cache or verified. *)
let use_fingerprint fingerprint : unit t =
 fun context ->
  ({ context with used_fingerprints = fingerprint :: context.used_fingerprints }, ())

let write cmd : unit t =
  let open State.Syntax in
  match cmd with
  | SmtLibAst.Assert _ ->
      Error.internal_error Loc.dummy
        "Cannot write assert command directly; use assume_expr instead"
  | _ ->
      let+ context = get_state in
      Session.write context.session cmd

let write_comment comment : unit t =
  let open State.Syntax in
  let+ context = get_state in
  Session.write_comment context.session comment

let with_scope (computation : 'a t) : 'a t =
 fun context -> Session.with_scope context.session ~f:(fun () -> computation context)

let push_path_condn term =
  let open State.Syntax in
  map_state ~f:(fun context ->
      { context with path_conditions = term :: context.path_conditions })

let pop_path_condn =
  let open State.Syntax in
  map_state ~f:(fun context ->
      { context with path_conditions = List.tl_exn context.path_conditions })

let under_path_conditions context expr =
  match context.path_conditions with
  | [] -> expr
  | conditions -> Expr.mk_impl (Expr.mk_and conditions) expr

let assume_expr ?name expr : unit t =
  let open State.Syntax in
  let+ context = get_state in
  let expr = under_path_conditions context expr |> Expr.drop_trivially_true in
  Session.assert_expr ?name context.session expr

let check_valid ?name expr : SmtSolver.validity_result t =
  let open State.Syntax in
  let+ context = get_state in
  Logs.debug (fun m -> m "Checking validity of %a" Expr.pr_verbose expr);
  let expr = under_path_conditions context expr in
  Session.check_valid ?name context.session expr

(** What a counterexample of a check made where the variables are at [state] asks for, if
    counterexamples are reported. *)
let counterexample_query (state : var_decl list) : Counterexample.query option t =
 fun context ->
  ( context,
    if context.counterexamples && not (List.is_empty state) then
      Some
        (Counterexample.query
           ~heap_field:(Hashtbl.find context.heap_fields)
           ~sequence_functions:context.sequence_functions ~branches:context.branches
           ~arms:context.arms state)
    else None )

(** Records from the symbol table [tbl] which types have the [length] and [index]
    functions of a sequence: those of the module of a type [M.T], if [M] declares both. *)
let set_sequence_functions (tbl : SymbolTbl.t) : unit t =
 fun context ->
  let sequence_functions (typ : type_expr) =
    match typ with
    | App (Var typ_name, [], _) when not (List.is_empty (QualIdent.path typ_name)) ->
        let member name =
          QualIdent.append (QualIdent.pop typ_name) (Ident.make Loc.dummy name 0)
        in
        let length = member "length" and index = member "index" in
        (* A member of a functor's instance is found through the instance. *)
        let is_func qual_ident =
          match SymbolTbl.resolve_and_find ~read_only:true qual_ident tbl with
          | Some (_, _, Module.CallDef { call_def = FuncDef _; _ }, _) -> true
          | _ -> false
        in
        Option.some_if (is_func length && is_func index) (length, index)
    | _ -> None
  in
  ({ context with sequence_functions }, ())

(** Records the fields of the program, from the symbol table [tbl], by the names of their
    heap variables. *)
let set_heap_fields (tbl : SymbolTbl.t) : unit t =
 fun context ->
  Map.iteri tbl.tbl_symbols ~f:(fun ~key ~data ->
      match data with
      | Module.FieldDef field when Option.is_none field.field_alias ->
          Hashtbl.set context.heap_fields
            ~key:(ProgUtils.serialize (QualIdent.to_string key) ^ "$Heap")
            ~data:(Ident.name field.field_name)
      | _ -> ());
  (context, ())

(** Like [check_valid], and what [model] makes of the model if the check fails (see
    [SmtSolver.SmtSession.check_valid_with_model]). *)
let check_valid_with_model ?name ~model expr : (SmtSolver.validity_result * 'a option) t =
  let open State.Syntax in
  let+ context = get_state in
  let expr = under_path_conditions context expr in
  Session.check_valid_with_model ?name context.session expr ~model
