open Base
open Ast
open ExtApi
open Util

module ExtName (Cont : Ext) = struct
  (* Every hook of `Ext` defaults to Cont's own behavior; only define the ones you
     actually override below. See docs/ext/README.md's Overview section. *)
  include Cont

  let lib_source = _
  (* let lib_source = Some ("extName_lib.rav", [%blob "extName_lib.rav"]) *)

  (* Declare whichever of these your extension actually needs -- delete the rest.
     See docs/ext/README.md's Overview and "Statement-bodied extensions" sections for
     which shape (flat `BasicStmtExt`, or self-contained `StmtExt`) fits your
     statement construct. *)
  type Type.type_ext +=
    | _

  type Expr.expr_ext +=
    | _

  type Stmt.stmt_ext +=
    | _ (* for a BasicStmtExt-shaped (flat, expr-list-only) statement *)
    | _ of { (* for a StmtExt-shaped (self-contained) statement, e.g. one that needs
                to carry a nested Stmt.t *)
      }

  type Stmt.contract_ext +=
    | _ of Stmt.spec list

  (* --- AstDef (docs/ext/README.md #astdef) --- *)

  let type_ext_to_name type_ext =
    match type_ext with
    | _ -> Cont.type_ext_to_name type_ext

  let expr_ext_to_string expr_ext =
    match expr_ext with
    | _ -> Cont.expr_ext_to_string expr_ext

  (* For a flat, basic_stmt_desc-level BasicStmtExt: *)
  let pr_basic_stmt_ext ppf ext expr_list =
    let open Stdlib.Format in
    match ext, expr_list with
    | _ -> Cont.pr_basic_stmt_ext ppf ext expr_list

  let basic_stmt_ext_symbols stmt_ext =
    match stmt_ext with
    | _ -> Cont.basic_stmt_ext_symbols stmt_ext

  let basic_stmt_ext_local_vars_modified stmt_ext exprs =
    match stmt_ext, exprs with
    | _ -> Cont.basic_stmt_ext_local_vars_modified stmt_ext exprs

  let basic_stmt_ext_fields_accessed stmt_ext exprs =
    match stmt_ext, exprs with
    | _ -> Cont.basic_stmt_ext_fields_accessed stmt_ext exprs

  (* For a self-contained, stmt_desc-level StmtExt instead: *)
  let pr_stmt_ext ppf stmt_ext =
    let open Stdlib.Format in
    match stmt_ext with
    | _ -> Cont.pr_stmt_ext ppf stmt_ext

  let stmt_ext_symbols stmt_ext =
    match stmt_ext with
    | _ -> Cont.stmt_ext_symbols stmt_ext

  let stmt_ext_local_vars_modified stmt_ext =
    match stmt_ext with
    | _ -> Cont.stmt_ext_local_vars_modified stmt_ext

  let stmt_ext_fields_accessed stmt_ext =
    match stmt_ext with
    | _ -> Cont.stmt_ext_fields_accessed stmt_ext

  (* Covers both statement extension points. Answer NoStep for a ghost statement
     and AtomicStep for one indivisible machine step; the base of the chain
     answers NonAtomicStep, barring the statement from atomic blocks. *)
  let stmt_ext_atomicity stmt_ext =
    match stmt_ext with
    | _ -> Cont.stmt_ext_atomicity stmt_ext

  let contract_ext_to_string contract_ext =
    match contract_ext with
    | _ -> Cont.contract_ext_to_string contract_ext

  let type_ext_is_recognized type_ext =
    match type_ext with
    | _ -> Cont.type_ext_is_recognized type_ext

  let expr_ext_is_recognized expr_ext =
    match expr_ext with
    | _ -> Cont.expr_ext_is_recognized expr_ext

  let stmt_ext_is_recognized stmt_ext =
    match stmt_ext with
    | _ -> Cont.stmt_ext_is_recognized stmt_ext

  let contract_ext_is_recognized contract_ext =
    match contract_ext with
    | _ -> Cont.contract_ext_is_recognized contract_ext

  (* --- Rewriter (docs/ext/README.md #rewriter) --- *)
  (* Only needed if a constructor above stores a type_expr (expr_ext_rewrite_types/
     basic_stmt_ext_rewrite_types) or a nested Stmt.t/expr (stmt_ext_rewrite), or for
     contract_ext_rewrite_exprs. *)

  let expr_ext_rewrite_types ~f expr_ext =
    match expr_ext with
    | _ -> Cont.expr_ext_rewrite_types ~f expr_ext

  let basic_stmt_ext_rewrite_types ~f stmt_ext =
    match stmt_ext with
    | _ -> Cont.basic_stmt_ext_rewrite_types ~f stmt_ext

  let stmt_ext_rewrite ~f ~c stmt_ext =
    match stmt_ext with
    | _ -> Cont.stmt_ext_rewrite ~f ~c stmt_ext

  let contract_ext_rewrite_exprs ~f contract_ext =
    match contract_ext with
    | _ -> Cont.contract_ext_rewrite_exprs ~f contract_ext

  (* --- Typing (docs/ext/README.md #typing) --- *)

  let type_check_type_expr (type_ext : Type.type_ext) (type_args : type_expr list)
      (type_attr : Type.type_attr) (type_check_type_expr_functs : type_check_type_expr_functs) =
    match type_ext, type_args with
    | _ -> Cont.type_check_type_expr type_ext type_args type_attr type_check_type_expr_functs

  let type_check_expr (expr_ext : Expr.expr_ext) (expr_list : expr list)
      (expr_attr : Expr.expr_attr) (expected_typ : type_expr)
      (type_check_expr_functs : type_check_expr_functs) =
    match expr_ext, expr_list with
    | _ -> Cont.type_check_expr expr_ext expr_list expr_attr expected_typ type_check_expr_functs

  (* For a flat BasicStmtExt: *)
  let type_check_basic_stmt call_decl (stmt_ext : Stmt.stmt_ext) (expr_list : expr list)
      (stmt_loc : Loc.t) (disam_tbl : ProgUtils.DisambiguationTbl.t)
      (type_check_stmt_functs : type_check_stmt_functs) :
      (Stmt.basic_stmt_desc * ProgUtils.DisambiguationTbl.t) Rewriter.t =
    match stmt_ext, expr_list with
    | _ -> Cont.type_check_basic_stmt call_decl stmt_ext expr_list stmt_loc disam_tbl type_check_stmt_functs

  (* For a self-contained StmtExt instead (see AssertWithExt for a real example,
     including how to type-check a nested proof block via type_check_stmt_functs'
     process_stmt): *)
  let type_check_stmt_ext call_decl (stmt_ext : Stmt.stmt_ext) (loc : location)
      (disam_tbl : ProgUtils.DisambiguationTbl.t)
      (type_check_stmt_functs : type_check_stmt_functs) :
      (Stmt.stmt_desc * ProgUtils.DisambiguationTbl.t) Rewriter.t =
    match stmt_ext with
    | _ -> Cont.type_check_stmt_ext call_decl stmt_ext loc disam_tbl type_check_stmt_functs

  let type_check_contract_ext call_decl (contract_ext : Stmt.contract_ext) (loc : location)
      (disam_tbl : ProgUtils.DisambiguationTbl.t)
      (type_check_stmt_functs : type_check_stmt_functs) : Stmt.contract_ext Rewriter.t =
    match contract_ext with
    | _ -> Cont.type_check_contract_ext call_decl contract_ext loc disam_tbl type_check_stmt_functs

  let check_contract_ext_group_compatible call_decls =
    Cont.check_contract_ext_group_compatible call_decls

  (* --- Rewrites (docs/ext/README.md #rewrites, #statement-bodied-extensions-stmtext-at-the-stmt_desc-level, #contracts) --- *)

  let rewrite_type_ext (type_ext : Type.type_ext) (tp_list : type_expr list) (loc : location) =
    match type_ext, tp_list with
    | _ -> Cont.rewrite_type_ext type_ext tp_list loc

  let rewrite_expr_ext (expr_ext : Expr.expr_ext) (expr_list : expr list)
      (expr_attr : Expr.expr_attr) =
    match expr_ext, expr_list with
    | _ -> Cont.rewrite_expr_ext expr_ext expr_list expr_attr

  let rewrite_basic_stmt_ext (stmt_ext : Stmt.stmt_ext) (expr_list : expr list) loc :
      Stmt.t Rewriter.t =
    match stmt_ext, expr_list with
    | _ -> Cont.rewrite_basic_stmt_ext stmt_ext expr_list loc

  let rewrite_stmt_ext (stmt_ext : Stmt.stmt_ext) (loc : location) : Stmt.t Rewriter.t =
    match stmt_ext with
    | _ -> Cont.rewrite_stmt_ext stmt_ext loc

  let rewrite_contract_ext_call caller_call_decl callee_call_decl in_same_scc call_args loc =
    Cont.rewrite_contract_ext_call caller_call_decl callee_call_decl in_same_scc call_args loc

  let rewrite_callable_entry call_decl = Cont.rewrite_callable_entry call_decl

  let rewrite_contract_ext_loop_transfer ~subst contract_ext =
    Cont.rewrite_contract_ext_loop_transfer ~subst contract_ext

  (* --------------------- *)
  (* --- DO NOT MODIFY --- *)
  let lib_sources = (Option.to_list lib_source) @ Cont.lib_sources
end
