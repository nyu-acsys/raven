open Base
open Ast
open ExtApi
open Util

(* This is the blank extension used to close the "chain" of extensions. If the code reaches this extension then that means that previous extensions did not do their job. This function mostly just raises errors for everything. *)

module DefaultExt = struct
  let lib_source = None

  (* AstDef *)
  let type_ext_to_name type_ext =
    Error.internal_error Loc.dummy "unhandled type extension (no active extension recognizes this type)"

  let expr_ext_to_string expr_ext =
    Error.internal_error Loc.dummy "unhandled expression extension (no active extension recognizes this expression)"
  let pr_stmt_ext ppf =
    Error.internal_error Loc.dummy "unhandled statement extension (no active extension recognizes this statement)"
  let contract_ext_to_string (contract_ext: Stmt.contract_ext) : string =
    Error.internal_error Loc.dummy "unhandled contract extension (no active extension recognizes this contract clause)"

  let stmt_ext_symbols _ = Set.empty (module QualIdent)
  let stmt_ext_local_vars_modified stmt_ext exprs = []
  let stmt_ext_fields_accessed stmt_ext exprs = []

  (* Base of the chain: this extension declares no constructors of its own. *)
  let type_ext_is_recognized (_: Type.type_ext) = false
  let expr_ext_is_recognized (_: Expr.expr_ext) = false
  let stmt_ext_is_recognized (_: Stmt.stmt_ext) = false
  let contract_ext_is_recognized (_: Stmt.contract_ext) = false


  (* Rewriter *)
  let expr_ext_rewrite_types ~(f: type_expr -> type_expr Rewriter.t) expr_ext =
    Rewriter.return expr_ext

  let stmt_ext_rewrite_types ~(f: type_expr -> type_expr Rewriter.t) stmt_ext =
    Rewriter.return stmt_ext

  let contract_ext_rewrite_exprs ~(f: expr -> expr Rewriter.t) (contract_ext: Stmt.contract_ext) : Stmt.contract_ext Rewriter.t =
    Error.internal_error Loc.dummy "unhandled contract extension reached the rewrite phase"


  (* Typing *)

  (* If some other `--extension` chain (not the active one) would have recognized this
     construct, name it instead of just saying nothing did -- see
     [suggest_extension_for_type_ext] & co. in Ast.Rewriter.ext_hooks. *)
  let extension_mismatch_error loc ext_name construct =
    Error.error loc
      (Printf.sprintf "this %s belongs to the `%s` extension; re-run with `--extension %s`" construct ext_name ext_name)

  let type_check_type_expr (type_ext: Type.type_ext) (type_args: type_expr list) (type_attr: Type.type_attr) (type_check_type_expr_functs: type_check_type_expr_functs) =
    let open Rewriter.Syntax in
    let* ext_hooks = Rewriter.current_ext_hooks in
    match ext_hooks.suggest_extension_for_type_ext type_ext with
    | Some ext_name -> extension_mismatch_error type_attr.type_loc ext_name "type"
    | None -> Error.internal_error type_attr.type_loc "unhandled type extension reached type-checking (no active extension recognizes this type)"

  let type_check_expr (a: Expr.expr_ext) (exprs: expr list) (expr_attr : Expr.expr_attr) (expected_typ: type_expr) (type_check_expr_functs: type_check_expr_functs): expr Rewriter.t =
    let open Rewriter.Syntax in
    let* ext_hooks = Rewriter.current_ext_hooks in
    match ext_hooks.suggest_extension_for_expr_ext a with
    | Some ext_name -> extension_mismatch_error expr_attr.expr_loc ext_name "expression"
    | None -> Error.internal_error expr_attr.expr_loc "unhandled expression extension reached type-checking (no active extension recognizes this expression)"

  let type_check_stmt (call_decl: Callable.call_decl) (stmt_ext: Stmt.stmt_ext) (expr_list: expr list) (loc: location) (disamTbl: ProgUtils.DisambiguationTbl.t) (type_check_stmt_functs: type_check_stmt_functs) =
    let open Rewriter.Syntax in
    let* ext_hooks = Rewriter.current_ext_hooks in
    match ext_hooks.suggest_extension_for_stmt_ext stmt_ext with
    | Some ext_name -> extension_mismatch_error loc ext_name "statement"
    | None -> Error.internal_error loc "unhandled statement extension reached type-checking (no active extension recognizes this statement)"

  let type_check_contract_ext (call_decl: Callable.call_decl) (contract_ext: Stmt.contract_ext) (loc: location) (disamTbl: ProgUtils.DisambiguationTbl.t) (type_check_stmt_functs: type_check_stmt_functs) =
    let open Rewriter.Syntax in
    let* ext_hooks = Rewriter.current_ext_hooks in
    match ext_hooks.suggest_extension_for_contract_ext contract_ext with
    | Some ext_name -> extension_mismatch_error loc ext_name "contract clause"
    | None -> Error.internal_error loc "unhandled contract extension reached type-checking (no active extension recognizes this contract clause)"


  (* Rewrites *)
  let rewrite_type_ext _ _ loc =
    Error.internal_error loc "unhandled type extension reached the rewrite phase"

  let rewrite_expr_ext _ _ (expr_attr: Expr.expr_attr) =
    Error.internal_error expr_attr.expr_loc "unhandled expression extension reached the rewrite phase"

  let rewrite_stmt_ext _ _ loc =
    Error.internal_error loc "unhandled statement extension reached the rewrite phase"

  (* Base of the chain: no more extensions to contribute recursive-call checks. *)
  let rewrite_contract_ext_call (_caller_call_decl: Callable.call_decl) (_callee_call_decl: Callable.call_decl) (_call_args: expr list) (_loc: location) : Stmt.t list Rewriter.t =
    Rewriter.return []

  let rewrite_callable_entry (_call_decl: Callable.call_decl) : Stmt.t list Rewriter.t =
    Rewriter.return []

  let rewrite_contract_ext_loop_transfer ~(subst: expr -> expr) (tag: Stmt.contract_ext) : Stmt.contract_ext = tag


  (* --------------------- *)
  (* --- DO NOT MODIFY --- *)
  let lib_sources = []
end