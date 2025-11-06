open Base
open Ast
open ExtApi
open Util

module DefaultExt = struct
  let expr_ext_to_string expr_ext =
    Error.internal_error Loc.dummy "Unhandled expr extension in DefaultExt.expr_ext_to_string."
  let pr_stmt_ext ppf = 
    Error.internal_error Loc.dummy "Unhandled stmt extension in DefaultExt.pr_basic_stmt."

  let stmt_ext_local_vars_modified stmt_ext exprs = []
  let stmt_ext_fields_accessed stmt_ext exprs = []

  let type_check_expr (a: Expr.expr_ext) (exprs: expr list) (expr_attr : Expr.expr_attr): expr Rewriter.t =
    Error.internal_error expr_attr.expr_loc "Unhandled Expr extension in DefaultExt.type_check_expr."

  let type_check_stmt (call_decl: Callable.call_decl) (stmt_ext: Stmt.stmt_ext) (expr_list: expr list) (loc: location) (disamTbl: ProgUtils.DisambiguationTbl.t) (type_check_stmt_functs: type_check_stmt_functs) =
      Error.internal_error loc "Unhandled stmt extension in DefaultExt.type_check_stmt"


  let rewrite_expr_ext _ _ loc =
    Error.internal_error loc "Unhandled stmt extension in DefaultExt.rewrite_expr_ext"

  let rewrite_stmt_ext _ _ loc = 
    Error.internal_error loc "Unhandled stmt extension in DefaultExt.rewrite_stmt_ext"
end