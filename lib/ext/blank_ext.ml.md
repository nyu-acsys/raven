open Base
open Ast
open ExtApi
open Util

module ExtName (Cont : Ext) = struct
  let lib_source = _
  let local_vars = _

  type Expr.expr_ext +=
    | _

  type Stmt.stmt_ext +=
    | _

  (* AstDef *)
  let expr_ext_to_string expr_ext =
    match expr_ext with 
    | _ -> Cont.expr_ext_to_string expr_ext

  let pr_stmt_ext ppf ext expr_list = 
    let open Stdlib.Format in
    match ext, expr_list with
    | _ -> Cont.pr_stmt_ext ppf ext expr_list

  let stmt_ext_symbols stmt_ext =
    match stmt_ext with
    | _ -> Cont.stmt_ext_symbols stmt_ext

  let stmt_ext_local_vars_modified stmt_ext exprs =
    match stmt_ext, exprs with
    | _ -> Cont.stmt_ext_local_vars_modified stmt_ext exprs
  
  let stmt_ext_fields_accessed stmt_ext exprs = 
    match stmt_ext, exprs with
    | _ -> Cont.stmt_ext_fields_accessed stmt_ext exprs

  (* Typing *)
  let type_check_expr (expr_ext: Expr.expr_ext) (expr_list: expr list) = 
    match expr_ext, expr_list with
    | _ -> Cont.type_check_expr expr_ext expr_list

  let type_check_stmt call_decl (stmt_ext : Stmt.stmt_ext) (expr_list: expr list) (stmt_loc: Loc.t) (disam_tbl : ProgUtils.DisambiguationTbl.t)
      (type_check_stmt_functs : ExtApi.type_check_stmt_functs)
  :
      (Stmt.basic_stmt_desc * ProgUtils.DisambiguationTbl.t) Rewriter.t = 
    let open Rewriter.Syntax in
    let* is_ghost_scope = Rewriter.is_ghost_scope in
    match stmt_ext, expr_list with
    | _ -> Cont.type_check_stmt call_decl stmt_ext expr_list stmt_loc disam_tbl type_check_stmt_functs


  (* Rewrites *)
  let rewrite_expr_ext (expr_ext: Expr.expr_ext) (expr_list: expr list) (loc: location) = 
    match expr_ext, expr_list with
    | _ -> Cont.rewrite_expr_ext expr_ext expr_list loc

  let rewrite_stmt_ext (stmt_ext: Stmt.stmt_ext) (expr_list: expr list) loc: Stmt.t Rewriter.t =
    let open Rewriter.Syntax in
    match stmt_ext, expr_list with
    | _ -> Cont.rewrite_stmt_ext stmt_ext expr_list loc

  (* --------------------- *)
  
  (* --- DO NOT MODIFY --- *)
  let lib_sources = (Option.to_list lib_source) @ Cont.lib_sources
  let ext_local_vars = local_vars @ Cont.ext_local_vars
end