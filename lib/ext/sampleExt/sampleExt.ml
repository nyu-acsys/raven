open Base
open Ast
open ExtApi
open Util

module SampleExt (Cont : Ext) = struct

  let lib_source = Some ("sampleExt_lib.rav", [%blob "sampleExt_lib.rav"])

  let local_vars = []

  type Stmt.stmt_ext +=
    | RandEven

  (* AstDef *)
  let type_ext_to_name = Cont.type_ext_to_name
  let expr_ext_to_string = Cont.expr_ext_to_string

  let pr_stmt_ext ppf ext expr_list = 
    let open Stdlib.Format in
    match ext, expr_list with
    | RandEven, [lhs_expr; n_expr] ->
      fprintf ppf "@[<2>[EXT]%a@ :=@ %s(%a)@]" Expr.pr lhs_expr "Rand" Expr.pr n_expr
    | RandEven, _ ->
      Error.internal_error Loc.dummy "[EXT] SampleExt.pr_stmt_ext: Incorrect number of arguments for randEven()" 
    | _ -> Cont.pr_stmt_ext ppf ext expr_list

  let stmt_ext_symbols stmt_ext =
    match stmt_ext with
    | RandEven -> Set.empty (module QualIdent)
    | _ -> Cont.stmt_ext_symbols stmt_ext

  let stmt_ext_local_vars_modified stmt_ext exprs =
    match stmt_ext, exprs with
    | RandEven, [lhs_expr; n_expr] ->
      let lhs_qi = Expr.to_qual_ident lhs_expr in
      if QualIdent.is_local lhs_qi then [QualIdent.to_ident lhs_qi] else []
    | RandEven, _ ->
      Error.internal_error Loc.dummy "[EXT] SampleExt.stmt_ext_local_vars_modified: Incorrect number of arguments for randEven()" 
    | _ -> Cont.stmt_ext_local_vars_modified stmt_ext exprs
  
  let stmt_ext_fields_accessed stmt_ext exprs = 
    match stmt_ext, exprs with
    | RandEven, _ -> []
    | _ -> Cont.stmt_ext_fields_accessed stmt_ext exprs


  (* Rewriter *)
  let expr_ext_rewrite_types = Cont.expr_ext_rewrite_types
  let stmt_ext_rewrite_types = Cont.stmt_ext_rewrite_types


  (* Typing *)
  let type_check_type_expr = Cont.type_check_type_expr
  let type_check_expr = Cont.type_check_expr

  let type_check_stmt call_decl (stmt_ext : Stmt.stmt_ext) (expr_list: expr list) (stmt_loc: Loc.t) (disam_tbl : ProgUtils.DisambiguationTbl.t)
      (type_check_stmt_functs : ExtApi.type_check_stmt_functs)
  :
      (Stmt.basic_stmt_desc * ProgUtils.DisambiguationTbl.t) Rewriter.t = 
    let open Rewriter.Syntax in
    match stmt_ext, expr_list with
    | RandEven, [lhs_expr; n_expr] ->
      let* lhs_qual_ident, var_decl = type_check_stmt_functs.get_assign_lhs (Expr.to_qual_ident lhs_expr) ~is_init:false in

      let* var_type_expanded = type_check_stmt_functs.expand_type_expr var_decl.var_type in

      if Type.(not (var_type_expanded = Type.int)) then
        type_check_stmt_functs.type_mismatch_error stmt_loc Type.int var_decl.var_type
      else
        let* n_expr = type_check_stmt_functs.disambiguate_process_expr n_expr Type.int disam_tbl in

        Rewriter.return (Stmt.StmtExt (RandEven, [Expr.from_var_decl var_decl; n_expr]), disam_tbl)

    | RandEven, _ ->
      Error.type_error stmt_loc "[EXT] SampleExt.stmt_ext_local_vars_modified: Incorrect number of arguments for randEven()"

    | _ -> Cont.type_check_stmt call_decl stmt_ext expr_list stmt_loc disam_tbl type_check_stmt_functs


  (* Rewrites *)
  let rewrite_type_ext = Cont.rewrite_type_ext
  
  let rewrite_expr_ext = Cont.rewrite_expr_ext

  let rewrite_stmt_ext (stmt_ext: Stmt.stmt_ext) (expr_list: expr list) loc: Stmt.t Rewriter.t =
    match stmt_ext, expr_list with
    | RandEven, [lhs_expr; n_expr] ->
      let havoc_stmt = Stmt.mk_havoc ~loc (Expr.to_qual_ident lhs_expr) in

      let inhale_stmt = 
        Stmt.mk_inhale_expr
          ~cmnt:("[EXT] SampleExt: RandEven postcondition")
          ~loc
          (Expr.mk_and ~loc 
          [ Expr.mk_app ~typ:Type.bool Leq [(Expr.mk_int 0); lhs_expr];
            Expr.mk_app ~typ:Type.bool Lt [lhs_expr; n_expr];
            (Expr.mk_eq ~loc
              (Expr.mk_app ~typ:Type.int Mod [lhs_expr; Expr.mk_int 2])
              (Expr.mk_int 0)
            )
          ])
      in

      Rewriter.return (Stmt.mk_block_stmt ~loc [havoc_stmt; inhale_stmt])
    
    | _ -> Cont.rewrite_stmt_ext stmt_ext expr_list loc


  (* --------------------- *)
  (* --- DO NOT MODIFY --- *)
  let lib_sources = (Option.to_list lib_source) @ Cont.lib_sources
  let ext_local_vars = local_vars @ Cont.ext_local_vars
end