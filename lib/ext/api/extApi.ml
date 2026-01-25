open Ast

(** Set of functions from Typing.ml available for type checking `Type.type_ext`  *)
type type_check_type_expr_functs = {
  process_type_expr : type_expr -> type_expr Rewriter.t;
}

(** Set of functions from Typing.ml available for type checking `Expr.expr_ext`  *)
type type_check_expr_functs = {
  check_and_set : expr -> type_expr -> type_expr -> type_expr -> expr Rewriter.t;
  process_expr : expr -> type_expr -> expr Rewriter.t;
  type_mismatch_error : 'a. location -> type_expr -> type_expr -> 'a;
  expand_type_expr : type_expr -> (type_expr, unit) Ast__Rewriter.t_ext;
}

(** Set of functions from Typing.ml available for type checking `Stmt.stmt_ext`  *)
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

(* Main Extension API *)
module type Ext = sig
  (* Config *)
  val lib_source : (string * string) option
  val local_vars : var_decl list

  (* AstDef *)
  val type_ext_to_name : (Type.type_ext -> string)

  val expr_ext_to_string : (Expr.expr_ext -> string)

  val pr_stmt_ext : Stdlib.Format.formatter -> Stmt.stmt_ext -> expr list -> unit

  val stmt_ext_symbols: Stmt.stmt_ext -> QualIdentSet.t
  val stmt_ext_local_vars_modified : Stmt.stmt_ext -> expr list -> ident list
  val stmt_ext_fields_accessed : Stmt.stmt_ext -> expr list -> qual_ident list


  (* Rewriter *)
  val expr_ext_rewrite_types :
    f:(type_expr -> type_expr Rewriter.t)
    -> Expr.expr_ext 
    -> Expr.expr_ext Rewriter.t

  val stmt_ext_rewrite_types :
    f: (type_expr -> type_expr Rewriter.t) 
    -> Stmt.stmt_ext 
    -> Stmt.stmt_ext Rewriter.t


  (* Typing *)
  val type_check_type_expr : Type.type_ext -> type_expr list -> Type.type_attr -> type_check_type_expr_functs -> type_expr Rewriter.t

  val type_check_expr : Expr.expr_ext -> expr list -> Expr.expr_attr -> type_expr -> type_check_expr_functs -> expr Rewriter.t

  val type_check_stmt : 
    Callable.call_decl ->
    Stmt.stmt_ext -> expr list ->
    location ->
    ProgUtils.DisambiguationTbl.t ->
    type_check_stmt_functs ->
    (Stmt.basic_stmt_desc * ProgUtils.DisambiguationTbl.t) Rewriter.t


  (* Rewrites *)
  val rewrite_type_ext : Ast.Type.type_ext -> type_expr list -> location -> type_expr Rewriter.t

  val rewrite_expr_ext : Expr.expr_ext -> expr list -> Expr.expr_attr -> expr Rewriter.t
  
  val rewrite_stmt_ext : Stmt.stmt_ext -> expr list -> location -> Stmt.t Rewriter.t

  val lib_sources : (string * string) list
  val ext_local_vars : var_decl list
end


module type ListFns = sig
    val listTpConstr : unit -> Type.type_ext
    val mk_list_tp : location -> type_expr -> type_expr 
    val ls_cons : location -> expr -> expr -> expr
    val ls_nil : location -> elem_typ:type_expr -> unit -> expr
    val ls_hd : location -> expr -> expr
    val ls_tl : location -> expr -> expr
    val ls_len : location -> expr -> expr
    val list_tp_to_elem_typ : type_expr -> type_expr option
  end

(* ListAPI for extensions that depend on lists such as ProphecyExt and ErrorCreditsExt *)
module type ListApi = sig
  include Ext

  module ListFns: ListFns
end