open Ast

module type ListApi = sig
  include ExtApi.Ext

  val listTpConstr : unit -> Type.type_ext

  val mk_list_tp : location -> type_expr -> type_expr 

  val ls_cons : location -> expr -> expr -> expr

  val ls_nil : location -> elem_typ:type_expr -> unit -> expr

  val ls_hd : location -> expr -> expr
  val ls_tl : location -> expr -> expr

  val ls_len : location -> expr -> expr

  val list_tp_to_elem_typ : type_expr -> type_expr option
end