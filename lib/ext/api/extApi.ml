open Ast

  type type_check_expr_functs = {
    check_and_set : expr -> type_expr -> type_expr -> type_expr -> expr Rewriter.t;
    process_expr : expr -> type_expr -> expr Rewriter.t;
  }

  type type_check_stmt_functs = {
    get_assign_lhs :  is_init:bool -> 
                      ?is_ghost_cmd:bool -> 
                      qual_ident -> 
                      unit Rewriter.state -> 
                      unit Rewriter.state * (qual_ident * var_decl);

    expand_type_expr : type_expr -> (type_expr, unit) Ast__Rewriter.t_ext;

    disambiguate_process_expr : expr -> type_expr -> ProgUtils.DisambiguationTbl.t -> expr Rewriter.t;

    type_mismatch_error : 'a. location -> type_expr -> type_expr -> 'a;

    disam_tbl_add_var_decl : var_decl -> ProgUtils.DisambiguationTbl.t -> var_decl * ProgUtils.DisambiguationTbl.t;

    process_symbol_ref : (Module.symbol -> Module.symbol Rewriter.t) ref;
  }

module type Ext = sig
  val lib_source : (string * string) option
  val local_vars : var_decl list

  (* AstDef *)
  val expr_ext_to_string : (Expr.expr_ext -> string)

  val pr_stmt_ext : Stdlib.Format.formatter -> Stmt.stmt_ext -> expr list -> unit

  val stmt_ext_symbols: Stmt.stmt_ext -> QualIdentSet.t
  val stmt_ext_local_vars_modified : Stmt.stmt_ext -> expr list -> ident list
  val stmt_ext_fields_accessed : Stmt.stmt_ext -> expr list -> qual_ident list

  (* Typing *)
  val type_check_expr : Expr.expr_ext -> expr list -> Expr.expr_attr -> type_expr -> type_check_expr_functs -> expr Rewriter.t

  val type_check_stmt : 
    Callable.call_decl ->
    Stmt.stmt_ext -> expr list ->
    location ->
    ProgUtils.DisambiguationTbl.t ->
    type_check_stmt_functs ->
    (Stmt.basic_stmt_desc * ProgUtils.DisambiguationTbl.t) Rewriter.t


  (* Rewrites *)
  val rewrite_expr_ext : Expr.expr_ext -> expr list -> location -> expr Rewriter.t
  val rewrite_stmt_ext : Stmt.stmt_ext -> expr list -> location -> Stmt.t Rewriter.t

  val lib_sources : (string * string) list
  val ext_local_vars : var_decl list
end