open Base
open Ast
open Util
open Smt
module Session = SmtSolver.SmtSession

type focus = { extents : Loc.t list; assertion : string option }
(** What `--only` selects: the procedures declared within the [extents], and in them only
    the [assertion] of that name, if any. *)

type context = {
  session : SmtSolver.session;
  path_conditions : expr list;
  auto_dependencies : Dependencies.Graph.t;
  diagnostics : Diagnostics.t;  (** The run's, for the verification errors. *)
  focus : focus option;
}

type 'a t = context -> context * 'a

let create ?focus ~diagnostics session =
  {
    session;
    path_conditions = [];
    auto_dependencies = Dependencies.Graph.empty;
    diagnostics;
    focus;
  }

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
  (context, ())

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
