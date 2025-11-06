open Ast


  type type_check_stmt_functs = {
    get_assign_lhs :  is_init:bool -> 
                      ?is_ghost_cmd:bool -> 
                      qual_ident -> 
                      unit Rewriter.state -> 
                      unit Rewriter.state * (qual_ident * var_decl);

    expand_type_expr : type_expr -> (type_expr, unit) Ast__Rewriter.t_ext;

    disambiguate_process_expr : expr -> type_expr -> ProgUtils.DisambiguationTbl.t -> expr Rewriter.t
  }

module type Ext = sig

  (* AstDef *)
  val expr_ext_to_string : (Expr.expr_ext -> string)

  val pr_stmt_ext : Stdlib.Format.formatter -> Stmt.stmt_ext -> expr list -> unit

  val stmt_ext_local_vars_modified : Stmt.stmt_ext -> expr list -> ident list
  val stmt_ext_fields_accessed : Stmt.stmt_ext -> expr list -> qual_ident list

  (* Typing *)
  val type_check_expr : Expr.expr_ext -> expr list -> Expr.expr_attr -> expr Rewriter.t

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
end