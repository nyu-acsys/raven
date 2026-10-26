(** The interface of Raven for other tools, over the builders of [Ast.Surface] and the
    pipeline of [Driver]. *)

open Base
open Raven
open Util
module S = Ast.Surface

let version = 1

let print_to_channel pr channel value =
  let ppf = Stdlib.Format.formatter_of_out_channel channel in
  pr ppf value;
  Stdlib.Format.pp_print_flush ppf ()

module Loc = struct
  type t = Loc.t

  let make = Loc.make
  let none = Loc.dummy
  let start (loc : t) = loc.loc_start
  let stop (loc : t) = loc.loc_end
end

module Ident = struct
  type t = Ast.Ident.t

  let make ~loc name = Ast.Ident.make loc name 0
end

module Name = struct
  type t = Ast.QualIdent.t

  let make ~loc ?(path = []) name =
    Ast.QualIdent.make (List.map path ~f:(Ident.make ~loc)) (Ident.make ~loc name)

  let of_ident = Ast.QualIdent.from_ident
end

module Type = struct
  type t = Ast.Type.t

  let int = S.Type.int
  let bool = S.Type.bool
  let real = S.Type.real
  let ref = S.Type.ref
  let perm = S.Type.perm
  let infer = S.Type.any
  let map = S.Type.map
  let set = S.Type.set
  let fin_set = S.Type.fin_set
  let tuple = S.Type.tuple
  let named = S.Type.named
  let atomic_token = S.Type.atomic_token

  type variant = Ast.Type.variant_decl

  let variant ~loc name args =
    S.Type.variant ~loc name
      (List.map args ~f:(fun (arg, typ) -> S.Type.var_decl ~loc arg typ))

  let data = S.Type.data
end

module Var = struct
  type t = Ast.Type.var_decl

  let make ~loc ?ghost ?implicit name typ = S.Type.var_decl ~loc ?ghost ?implicit name typ
end

module Expr = struct
  type t = Ast.Expr.t

  let pr = Ast.Expr.pr
  let print = print_to_channel pr
  let to_string e = Stdlib.Format.asprintf "%a" pr e
  let alpha_equal e1 e2 = Ast.Expr.alpha_equal e1 e2
  let int = S.Expr.int
  let real = S.Expr.real
  let bool = S.Expr.bool
  let null = S.Expr.null
  let var = S.Expr.var
  let tuple = S.Expr.tuple
  let annotated = S.Expr.annotated
  let call = S.Expr.call
  let field ~loc e f = S.Expr.field ~loc e f
  let own = S.Expr.own
  let au = S.Expr.au
  let au_commit = S.Expr.au_commit
  let set = S.Expr.set
  let seq = S.Expr.seq
  let set_compr = S.Expr.set_compr
  let map_literal = S.Expr.map_literal
  let index = S.Expr.index
  let update = S.Expr.update
  let slice = S.Expr.slice
  let slice_from = S.Expr.slice_from
  let slice_to = S.Expr.slice_to
  let tuple_get ~loc e n = S.Expr.tuple_get ~loc e n
  let neg = S.Expr.neg
  let not_ = S.Expr.not_

  type case = Case of Ident.t * Ident.t list | Default

  let is_ ~loc e ctor = Ext.MatchExtInstance.mk_is ~loc e ctor

  let arm = function
    | Case (ctor, vars) -> { Ext.MatchExtInstance.arm_ctor = Some ctor; arm_vars = vars }
    | Default -> { arm_ctor = None; arm_vars = [] }

  let match_ ~loc e cases =
    Ext.MatchExtInstance.mk_match ~loc e
      (List.map cases ~f:(fun (c, body) -> (arm c, body)))

  type binop =
    | Mult
    | Div
    | Mod
    | Plus
    | Minus
    | Lt
    | Leq
    | Gt
    | Geq
    | Eq
    | Neq
    | Iff
    | And
    | Or
    | Impl
    | In
    | Not_in
    | Union
    | Inter
    | Diff
    | Subseteq
    | User of string

  let binary ~loc op e1 e2 =
    let op : S.Expr.binop =
      match op with
      | Mult -> Mult
      | Div -> Div
      | Mod -> Mod
      | Plus -> Plus
      | Minus -> Minus
      | Lt -> Lt
      | Leq -> Leq
      | Gt -> Gt
      | Geq -> Geq
      | Eq -> Eq
      | Neq -> Neq
      | Iff -> Iff
      | And -> And
      | Or -> Or
      | Impl -> Impl
      | In -> In
      | Not_in -> Not_in
      | Union -> Union
      | Inter -> Inter
      | Diff -> Diff
      | Subseteq -> Subseteq
      | User name -> User (Ident.make ~loc name)
    in
    S.Expr.binary ~loc op e1 e2

  let ite = S.Expr.ite
  let forall ~loc ?triggers vars body = S.Expr.forall ~loc ?triggers vars body
  let exists ~loc ?triggers vars body = S.Expr.exists ~loc ?triggers vars body
end

module Spec = struct
  type t = Ast.Stmt.spec

  let make ?(atomic = false) ?name ?(triggers = []) e =
    { (S.Stmt.spec ~atomic ?name e) with spec_trigs = triggers }
end

module Stmt = struct
  type t = Ast.Stmt.t
  type rhs = S.Stmt.rhs

  let expr_rhs = S.Stmt.expr_rhs
  let new_rhs = S.Stmt.new_rhs

  let local ~loc ?(ghost = false) ?(const = false) ?typ ?init name =
    S.Stmt.local_var_def ~ghost ~const (S.Type.local_decl ~loc name typ) init ~rhs_loc:loc
    |> List.map ~f:(S.Stmt.at ~loc)

  let assign ~loc lhs rhs = S.Stmt.at ~loc (S.Stmt.assign lhs rhs)
  let bind ~loc lhs e = S.Stmt.at ~loc (S.Stmt.bind lhs e)
  let call ~loc e = S.Stmt.at ~loc (S.Stmt.call e)
  let spawn ~loc callee args = S.Stmt.at ~loc (S.Stmt.spawn callee args)
  let havoc ~loc x = S.Stmt.at ~loc (S.Stmt.havoc x)
  let spec_stmt kind ~loc spec = S.Stmt.at ~loc (S.Stmt.spec_stmt kind spec)
  let assert_ = spec_stmt Assert
  let assume = spec_stmt Assume
  let inhale = spec_stmt Inhale
  let exhale = spec_stmt Exhale
  let return ~loc es = S.Stmt.at ~loc (S.Stmt.return ~loc es)

  let fold ~loc ?witnesses name args =
    S.Stmt.at ~loc (S.Stmt.use Fold name ?witnesses args)

  let unfold ~loc ?witnesses name args =
    S.Stmt.at ~loc (S.Stmt.use Unfold name ?witnesses args)

  let block ~loc stmts = S.Stmt.at ~loc (S.Stmt.block stmts)
  let ghost_block ~loc stmts = S.Stmt.at ~loc (S.Stmt.ghost_block stmts)
  let atomic_block ~loc stmts = S.Stmt.at ~loc (S.Stmt.atomic_block stmts)

  let match_ ~loc e cases =
    let case (c, body) = (Expr.arm c, S.Stmt.at ~loc (S.Stmt.block body)) in
    Ext.MatchExtInstance.mk_match_stmt ~loc e (List.map cases ~f:case)

  let if_ ~loc test then_ else_ =
    S.Stmt.at ~loc (S.Stmt.if_ ~then_loc:loc ~else_loc:loc test then_ else_)

  let while_ ~loc ?invariants test body =
    S.Stmt.at ~loc (S.Stmt.while_ ~loc ?invariants test (S.Stmt.block_stmt ~loc body))
end

module Callable = struct
  type t = Ast.Callable.t
  type proc_kind = Proc | Lemma | Axiom

  let opens_clause (loc, entries) : Ast.Callable.opens_clause =
    { opens_entries = entries; opens_loc = loc }

  let proc ~loc ?(kind = Proc) ?(atomic = false) ?(auto = false) ?formals ?returns
      ?(requires = []) ?(ensures = []) ?opens ?(decreases = []) name body =
    let kind : S.Callable.proc_kind =
      match kind with
      | Proc -> Proc
      | Lemma -> Lemma { is_auto = auto }
      | Axiom ->
          if Option.is_some body then
            invalid_arg "Raven_api.Callable.proc: an axiom has no body";
          Axiom { is_auto = auto }
    in
    let decl =
      S.Callable.decl ~loc ~kind:Func ?formals ?returns ~precond:requires
        ~postcond:ensures
        ?opens:(Option.map opens ~f:opens_clause)
        ~contract_ext:
          (match decreases with
          | [] -> []
          | measures ->
              [
                Ext.DecreasesExtInstance.Decreases
                  (List.map measures ~f:(fun e -> Spec.make e));
              ])
        name
    in
    S.Callable.proc ~atomic kind decl (Option.map body ~f:(S.Stmt.block_stmt ~loc))

  type func_kind = Func | Pred | Inv

  let func ~loc ?(kind = Func) ?(inline = false) ?formals ?returns ?(requires = [])
      ?(ensures = []) name body =
    let kind : Ast.Callable.call_kind =
      match kind with
      | Func -> Func
      | Pred -> Pred
      | Inv ->
          if inline then
            invalid_arg "Raven_api.Callable.func: an invariant cannot be inline";
          Invariant
    in
    let decl =
      S.Callable.decl ~loc ~kind ~is_inline:inline ?formals ?returns ~precond:requires
        ~postcond:ensures name
    in
    S.Callable.func decl body
end

module Member = struct
  type t = Ast.Module.module_instr

  let field ~loc ?(ghost = false) ?where name typ =
    S.Module.symbol (FieldDef (S.Module.field ~loc ~ghost ?where ~type_loc:loc name typ))

  let type_ ~loc ?(rep = false) name def =
    S.Module.symbol (TypeDef (S.Module.type_def ~loc ~rep name def))

  let value ~loc ?(ghost = false) ?(const = true) ?typ name init =
    S.Module.symbol
      (VarDef (S.Module.var_def ~ghost ~const (S.Type.local_decl ~loc name typ) init))

  let callable c = S.Module.symbol (CallDef c)
  let import ~loc ?all name = S.Module.import_member (S.Module.import ~loc ?all name)

  let module_with_parameters ~loc ~parameters ?interface ?(implements = []) ?sealed name
      members =
    let implements =
      List.map implements ~f:(fun (iface, args) -> (iface, List.map args ~f:S.Module.arg))
    in
    S.Module.symbol
      (S.Module.module_def ?interface
         (S.Module.header_with_parameters ~loc ~parameters ~implements ?sealed name)
         (S.Module.members members))

  let module_ ~loc ?interface ?(params = []) ?implements ?sealed name members =
    let params = List.map params ~f:(fun (param, typ) -> S.Module.param ~loc param typ) in
    module_with_parameters ~loc
      ~parameters:(Ast.Module.parameters_of_formals params)
      ?interface ?implements ?sealed name members

  let unit_factory ~loc ?interface ?implements ?sealed name members =
    module_with_parameters ~loc ~parameters:Ast.Module.UnitParameter ?interface
      ?implements ?sealed name members

  let instance ~loc ?def name typ =
    let def =
      Option.map def ~f:(fun (functor_, args) ->
          (functor_, List.map args ~f:S.Module.arg))
    in
    S.Module.symbol (S.Module.instance ~loc ?def name typ)

  let alias ~loc ?typ ?sealed name target =
    S.Module.symbol
      (S.Module.binding ~loc ~definition:(Ast.Module.Alias target) ?sealed name
         (Option.value typ ~default:target))

  let checked_view ~loc ~typ ?sealed name target =
    S.Module.symbol
      (S.Module.binding ~loc ~definition:(Ast.Module.Alias target) ~checked:true ?sealed
         name typ)

  let unit_instance ~loc ?typ name factory =
    S.Module.symbol
      (S.Module.binding ~loc ~definition:(Ast.Module.ApplyUnit factory) name
         (Option.value typ ~default:factory))

  let free : t -> t = function
    | SymbolDef symbol -> SymbolDef (Ast.Symbol.set_free symbol)
    | Import _ as member -> member
end

module Program = struct
  type t = Ast.Module.t

  let make ~loc members = S.Module.program ~loc (S.Module.members members)

  let pr ppf (program : t) =
    let (module E) = Ext.module_map Ext.ProphecyExt in
    SourcePrinting.pr ~hooks:(Ext.to_ext_hooks (module E : ExtApi.Ext)) ppf program

  let print = print_to_channel pr
  let to_string program = Stdlib.Format.asprintf "%a" pr program
end

module Diagnostic = struct
  type severity = Error | Warning
  type kind = Syntax | Type | Verification | Unsupported | Internal | Other

  type code =
    | Assertion
    | Loop_invariant_entry
    | Precondition
    | Postcondition
    | Fold
    | Unfold
    | Permission
    | Frame_preserving_update
    | Bind
    | Injectivity
    | Allocation
    | Commit
    | Abort
    | Uncommitted
    | Atomic_token
    | Implicit_agreement
    | Atomicity
    | Mask
    | Unclosed
    | Invariant_arguments
    | Atomic_update
    | Abortable_call
    | Extension of { extension : string; name : string }

  let to_error_code : code -> Error.code = function
    | Assertion -> Assertion
    | Loop_invariant_entry -> Loop_invariant_entry
    | Precondition -> Precondition
    | Postcondition -> Postcondition
    | Fold -> Fold
    | Unfold -> Unfold
    | Permission -> Permission
    | Frame_preserving_update -> Frame_preserving_update
    | Bind -> Bind
    | Injectivity -> Injectivity
    | Allocation -> Allocation
    | Commit -> Commit
    | Abort -> Abort
    | Uncommitted -> Uncommitted
    | Atomic_token -> Atomic_token
    | Implicit_agreement -> Implicit_agreement
    | Atomicity -> Atomicity
    | Mask -> Mask
    | Unclosed -> Unclosed
    | Invariant_arguments -> Invariant_arguments
    | Atomic_update -> Atomic_update
    | Abortable_call -> Abortable_call
    | Extension { extension; name } -> Extension { extension; name }

  let of_error_code : Error.code -> code = function
    | Assertion -> Assertion
    | Loop_invariant_entry -> Loop_invariant_entry
    | Precondition -> Precondition
    | Postcondition -> Postcondition
    | Fold -> Fold
    | Unfold -> Unfold
    | Permission -> Permission
    | Frame_preserving_update -> Frame_preserving_update
    | Bind -> Bind
    | Injectivity -> Injectivity
    | Allocation -> Allocation
    | Commit -> Commit
    | Abort -> Abort
    | Uncommitted -> Uncommitted
    | Atomic_token -> Atomic_token
    | Implicit_agreement -> Implicit_agreement
    | Atomicity -> Atomicity
    | Mask -> Mask
    | Unclosed -> Unclosed
    | Invariant_arguments -> Invariant_arguments
    | Atomic_update -> Atomic_update
    | Abortable_call -> Abortable_call
    | Extension { extension; name } -> Extension { extension; name }

  let code_name code = Error.code_name (to_error_code code)

  type related = { related_loc : Loc.t; related_message : string }

  type t = {
    severity : severity;
    kind : kind;
    code : code option;
    loc : Loc.t;
    message : string;
    related : related list;
  }

  let error_kind (d : t) : Error.error_kind =
    match (d.severity, d.kind) with
    | Warning, _ -> Warning
    | Error, Syntax -> Syntax
    | Error, Type -> Type
    | Error, Verification ->
        Verification (Option.value_map d.code ~default:Error.Assertion ~f:to_error_code)
    | Error, Unsupported -> Unsupported
    | Error, Internal -> Internal
    | Error, Other -> Generic

  let pr ppf d =
    Stdlib.Format.pp_print_string ppf (Error.to_string (error_kind d, d.loc, d.message));
    List.iter d.related ~f:(fun r ->
        Stdlib.Format.pp_print_char ppf '\n';
        Stdlib.Format.pp_print_string ppf
          (Error.to_string (RelatedLoc, r.related_loc, r.related_message)))

  let print = print_to_channel pr
  let to_string d = Stdlib.Format.asprintf "%a" pr d

  (** The diagnostics of Raven's [errors]: each error with the related locations,
      counterexamples and branches that follow it. *)
  let of_errors (errors : Error.t list) : t list =
    let primary (kind, loc, message) =
      let severity, kind, code =
        match (kind : Error.error_kind) with
        | Warning -> (Warning, Other, None)
        | Lexical | Syntax -> (Error, Syntax, None)
        | Type -> (Error, Type, None)
        | Verification code -> (Error, Verification, Some (of_error_code code))
        | Unsupported -> (Error, Unsupported, None)
        | Internal -> (Error, Internal, None)
        | Generic | Limit | RelatedLoc | Counterexample _ | Branch -> (Error, Other, None)
      in
      { severity; kind; code; loc; message; related = [] }
    in
    let add_related d (kind, loc, message) =
      let message =
        match (kind : Error.error_kind) with
        | RelatedLoc -> message
        | kind -> Error.error_kind_to_string kind ^ ": " ^ message
      in
      { d with related = { related_loc = loc; related_message = message } :: d.related }
    in
    let finish d = { d with related = List.rev d.related } in
    let rec go acc current = function
      | [] ->
          List.rev (Option.value_map current ~default:acc ~f:(fun d -> finish d :: acc))
      | ((kind, _, _) as error) :: errors -> (
          match ((kind : Error.error_kind), current) with
          | (RelatedLoc | Counterexample _ | Branch), Some d ->
              go acc (Some (add_related d error)) errors
          | _ ->
              let acc =
                Option.value_map current ~default:acc ~f:(fun d -> finish d :: acc)
              in
              go acc (Some (primary error)) errors)
    in
    go [] None errors
end

type extension = Default | Eris
type options = { extension : extension; smt_timeout : int; max_errors : int option }

let default_options = { extension = Default; smt_timeout = 10000; max_errors = None }

type result = { verified : bool; diagnostics : Diagnostic.t list }

let config_of (options : options) : Driver.config =
  {
    no_library = false;
    typecheck_only = false;
    lsp_mode = false;
    lsp_annotations = false;
    base_dir = "";
    prog_stats = false;
    smt_timeout = options.smt_timeout;
    smt_diagnostics = false;
    max_errors = options.max_errors;
    log_level = None;
    strict = false;
    only = None;
    counterexamples = false;
    fingerprints = false;
    cache_dir = None;
  }

(* A top-level handler, as the executable's: the errors that end a run are returned as
   diagnostics, never raised. *)
let verify ?(options = default_options) ?(includes = []) (program : Program.t) : result =
  let config = config_of options in
  let diagnostics =
    Diagnostics.create ?max_errors:options.max_errors ~collect_warnings:true ()
  in
  let include_sites = Driver.create_includes () in
  let extension =
    match options.extension with Default -> Ext.ProphecyExt | Eris -> Ext.ErisExt
  in
  let run () =
    Ast.Ident.restore ();
    let included =
      Driver.parse_program ~free:true ~includes:include_sites ~diagnostics config includes
    in
    Driver.check_program ~includes:include_sites ~extension_mode:(`Explicit extension)
      ~diagnostics config
      (Ast.merge_prog included program)
  in
  let errors =
    match run () with
    | () -> []
    | exception Error.Msg errors -> errors
    | exception Driver.Finished _ -> []
    | exception Unix.Unix_error (err, _, prog) ->
        [
          ( Internal,
            Loc.none,
            Printf.sprintf "Could not start '%s' (%s). Raven requires Z3 (>= %s)." prog
              (Unix.error_message err) Config.min_z3_version );
        ]
    | exception ((Sys_error _ | Failure _ | Invalid_argument _ | Assert_failure _) as exn)
      ->
        [ (Internal, Loc.none, Exn.to_string exn) ]
  in
  {
    verified = List.is_empty errors;
    diagnostics = Diagnostic.of_errors (Diagnostics.warnings diagnostics @ errors);
  }
