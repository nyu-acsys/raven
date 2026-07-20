open Base
open Ast
open ExtApi
open Util

(* This is the blank extension used to close the "chain" of extensions. If the code reaches this extension then that means that previous extensions did not do their job. This function mostly just raises errors for everything. *)

module DefaultExt = struct
  let lib_source = None
  let local_vars = []

  (* AstDef *)
  let type_ext_to_name type_ext =
    Error.internal_error Loc.dummy "unhandled type extension (no active extension recognizes this type)"

  let expr_ext_to_string expr_ext =
    Error.internal_error Loc.dummy "unhandled expression extension (no active extension recognizes this expression)"
  let pr_stmt_ext ppf =
    Error.internal_error Loc.dummy "unhandled statement extension (no active extension recognizes this statement)"

  let stmt_ext_symbols _ = Set.empty (module QualIdent)
  let stmt_ext_local_vars_modified stmt_ext exprs = []
  let stmt_ext_fields_accessed stmt_ext exprs = []


  (* Rewriter *)
  let expr_ext_rewrite_types ~(f: type_expr -> type_expr Rewriter.t) expr_ext =
    Rewriter.return expr_ext

  let stmt_ext_rewrite_types ~(f: type_expr -> type_expr Rewriter.t) stmt_ext = 
    Rewriter.return stmt_ext


  (* Typing *)
  let type_check_type_expr (type_ext: Type.type_ext) (type_args: type_expr list) (type_attr: Type.type_attr) (type_check_type_expr_functs: type_check_type_expr_functs) =
    Error.internal_error type_attr.type_loc "unhandled type extension reached type-checking (no active extension recognizes this type)"

  let type_check_expr (a: Expr.expr_ext) (exprs: expr list) (expr_attr : Expr.expr_attr) (expected_typ: type_expr) (type_check_expr_functs: type_check_expr_functs): expr Rewriter.t =
    Error.internal_error expr_attr.expr_loc "unhandled expression extension reached type-checking (no active extension recognizes this expression)"

  let type_check_stmt (call_decl: Callable.call_decl) (stmt_ext: Stmt.stmt_ext) (expr_list: expr list) (loc: location) (disamTbl: ProgUtils.DisambiguationTbl.t) (type_check_stmt_functs: type_check_stmt_functs) =
      Error.internal_error loc "unhandled statement extension reached type-checking (no active extension recognizes this statement)"


  (* Rewrites *)
  let rewrite_type_ext _ _ loc =
    Error.internal_error loc "unhandled type extension reached the rewrite phase"

  let rewrite_expr_ext _ _ (expr_attr: Expr.expr_attr) =
    Error.internal_error expr_attr.expr_loc "unhandled expression extension reached the rewrite phase"

  let rewrite_stmt_ext _ _ loc =
    Error.internal_error loc "unhandled statement extension reached the rewrite phase"


  (* --------------------- *)
  (* --- DO NOT MODIFY --- *)
  let lib_sources = []
  let ext_local_vars = []
end