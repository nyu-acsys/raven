(** Abstract syntax tree of a Raven program *)

open Base

(** Source code locations *)

module Loc = struct
  
  type position =
      { pos_lnum: int;
        pos_cnum: int;
      }
      [@@deriving compare, hash]
        
  type t =
      { loc_file: string;
        loc_start: position;
        loc_end: position;
      }
      [@@deriving compare, hash]
end

type location = Loc.t
    
(** Identifiers *)

module Ident = struct
  
  type t =
      { ident_name: string;
        ident_id: int;
      }
      [@@deriving compare, hash]

  let to_string id =
    match id.ident_id with
    | 0 -> id.ident_name
    | _ -> Printf.sprintf !"%{String}#%{Int}" id.ident_name id.ident_id
          
  let pr ppf id = Stdlib.Format.fprintf ppf "%s" (to_string id)
    
  let pr_list ppf ids = Util.pr_list_comma pr ppf ids
end

type ident = Ident.t
    
type 'a ident_map = (Ident.t, 'a) Hashtbl.Poly.t

(** Qualified identifiers *)

module QualIdent = struct      
  type t =
      { qual_path: Ident.t list;
        qual_base: Ident.t;
      }
      [@@deriving compare, hash]

  let pr ppf qid =
    Util.pr_list_sep "." Ident.pr ppf (qid.qual_path @ [qid.qual_base])

  let to_string qid = Util.string_of_format pr qid

end

type qual_ident = QualIdent.t
      
(** Types *)

module Type = struct
  
  type type_attr =
      { type_loc: Loc.t;
      }

  and t =
    | Int of type_attr
    | Bool of type_attr
    | Unit of type_attr
    | AnyRef of type_attr
    | Ref of QualIdent.t * type_attr
    | Perm of type_attr
    | Any of type_attr
    | Var of QualIdent.t * type_attr
    | Set of type_attr
    | Map of type_attr
    | App of t * t list * type_attr
    | Alias of QualIdent.t * t * type_attr
          (*| TypeData of qual_ident * type_attr*)
    | Dot of t * Ident.t * type_attr
    [@@deriving compare, hash]

  (** Pretty printing types *)        
          
  let ref_type_string = "Ref"
  let map_type_string = "Map"
  let set_type_string = "Set"
  let bool_type_string = "Bool"
  let int_type_string = "Int"
  let unit_type_string = "Unit"
  let perm_type_string = "Perm"
  let any_type_string = "Any"
  let anyref_type_string = "AnyRef"

  let to_name = function
  | Int _ -> int_type_string
  | Bool _ -> bool_type_string
  | Unit _ -> unit_type_string
  | Any _ -> any_type_string
  | AnyRef _ -> anyref_type_string
  | Set _ -> set_type_string
  | Map _ -> map_type_string
  | Perm _ -> perm_type_string
  | Ref (id, _)
  | Var (id, _)
  | Alias (id, _, _) -> QualIdent.to_string id
  | App _ -> "App"
  | Dot _ -> "Dot"
      
  let rec pr ppf t = match t with
  | Int _
  | Bool _
  | Unit _
  | Any _
  | AnyRef _
  | Perm _
  | Var _
  | Set _
  | Map _
  | Alias _
  | Ref _ ->
      Stdlib.Format.fprintf ppf "%s" (to_name t)
  | App (t1, ts, _) ->
      Stdlib.Format.fprintf ppf "%a[@[%a]]" pr t1 (Util.pr_list_comma pr) ts
  | Dot (t1, id, _) ->
      Stdlib.Format.fprintf ppf "%a.%a" pr t1 Ident.pr id
    
end

type type_expr = Type.t
          
(** Expressions *)
          
module Expr = struct

  type constr =
    (* Constants *)
    | Null
    | Unit
    | Bool of bool
    | Int of Int64.t
    | Empty
    (* Unary operators *)
    | Not | Uminus
    (* Binary operators *)
    | Eq | Gt | Lt | Geq | Leq
    | Diff | Union | Inter | Elem | Subseteq
    | And | Or
    | Plus | Minus | Mult | Div | Mod
    | Dot | Read
    (* Ternary operators *)
    | Ite | Write | Own
    (* Variable arity operators *)
    | Setenum
    | Var of qual_ident
      
  type binder =
    | Forall | Exists | Compr

  type var_decl =
      { var_name : ident;
        var_loc : location;
        var_type : type_expr;
      }
      
  type expr_attr =
      { expr_loc: location;
        expr_type: type_expr;
      }
        
  and t =
    (* Application expressions *)
    | App of constr * t list * expr_attr
    (* Variable binder expressions *)
    | Binder of binder * var_decl list * t * expr_attr

  let attr_of = function
    | App (_, _, attr)
    | Binder (_, _, _, attr) -> attr
          
  let to_loc t = t |> attr_of |> (fun attr -> attr.expr_loc) 
          
  let to_type t = t |> attr_of |> (fun attr -> attr.expr_type) 
          
  (** Pretty printing expressions *)

  let constr_to_string = function
  (* function symbols *)
  | Bool b -> Printf.sprintf "%b" b
  | Int i -> Int64.to_string i
  | Null -> "null"
  | Unit -> "()"
  | Dot -> "."
  | Read -> "read"
  | Write -> "write"
  | Uminus -> "-"
  | Plus -> "+"
  | Minus -> "-"
  | Mult -> "*"
  | Div -> "/"
  | Mod -> "%"
  | Empty -> "{||}"
  | Setenum -> "{||}"
  | Union -> "++"
  | Inter -> "**"
  | Diff -> "--"
  | Ite -> "ite"
  (* predicate symbols *)
  | Eq -> "=="
  | Leq -> "<="
  | Geq -> ">="
  | Lt -> "<"
  | Gt -> ">"
  | Elem -> "in"
  | Subseteq -> "subsetof"
  | And -> "&&"
  | Not -> "!"
  | Or -> "||"
  (* variables / uninterpreted symbols *)
  | Var id -> QualIdent.to_string id
  (* ownership predicates *)
  | Own -> "own"      
        
    
  let pr_constr ppf c = Stdlib.Format.fprintf ppf "%s" (constr_to_string c)
  
  let constr_to_prio = function
    | Null | Unit | Empty | Int _ | Bool _ -> 0
    | Dot | Setenum | Read | Write | Own | Var _ -> 1
    | Uminus | Not -> 2 
    | Mult | Div | Mod -> 3
    | Minus | Plus -> 4
    | Diff | Union | Inter -> 6
    | Gt | Lt | Geq | Leq | Elem | Subseteq -> 7
    | Eq -> 8
    | And -> 12
    | Or -> 16
    | Ite -> 17
          
  let to_prio = function
    | App (c, _, _) -> constr_to_prio c
    | Binder (Compr, _, _, _) -> 0
    | Binder ((Forall | Exists), _, _, _) -> 18

  let binder_to_string = function
    | Exists -> "exists"
    | Forall -> "forall"
    | Compr -> "%compr%"
          
  let rec pr ppf e =
    let open Stdlib.Format in
    match e with
    | App ((Union | Setenum), [], a) -> pr ppf (App(Empty, [], a))
    | App (Inter, [], _) -> fprintf ppf "Univ"
    | App (c, [], _) -> fprintf ppf "%a" pr_constr c
    | App (Dot, [e2; e1], _) | App (Read, [e1; e2], _) ->
        (match e1, to_type e2 with
        | App (Var _, _, _), (Ref _ | AnyRef _) ->
            fprintf ppf "%a.%a" pr e2 pr e1
        | _ ->
            fprintf ppf "%a(%a)" pr e1 pr e2)
    | App (Write, [e1; e2; e3], _) ->
      fprintf ppf "%a[|%a := %a|]" pr e1 pr e2 pr e3
    | App ((Minus | Plus | Mult | Div | Mod | Diff | Inter | Union
            | Eq | Subseteq | Leq | Geq | Lt | Gt | Elem | And | Or as c), [e1; e2], _) ->
      let pr_e1 = 
        if constr_to_prio c < to_prio e1
        then pr_paran
        else pr
      in
      let pr_e2 =
        if constr_to_prio c <= to_prio e2
        then pr_paran
        else pr
      in        
      fprintf ppf "@[<2>%a %a@ %a@]" pr_e1 e1 pr_constr c pr_e2 e2
  | App (Setenum, es, _) -> 
      fprintf ppf "{|@[%a@]|}" pr_list es
  | App (c, es, _) -> fprintf ppf "%a(@[%a@])" pr_constr c pr_list es
  | Binder (b, vs, e1, _) ->
      fprintf ppf "@[%a@]" pr_binder (b, vs, e1, to_type e)
  and pr_list ppf = Util.pr_list_comma pr ppf 
  and pr_paran ppf = Stdlib.Format.fprintf ppf "(%a)" pr
  and pr_binder ppf = function
    | ((Forall | Exists as b), vs, e, _) ->
        Stdlib.Format.fprintf ppf "%s@ %a@ ::@ %a" (binder_to_string b) pr_var_decl_list vs pr e
    | (Compr, vs, e, App (Set _, _, _)) ->
        Stdlib.Format.fprintf ppf "{|@ %a@ ::@ %a@ |}" pr_var_decl_list vs pr e
    | (Compr, vs, e, _) ->
        Stdlib.Format.fprintf ppf "[|@ %a@ ::@ %a@ |]" pr_var_decl_list vs pr e
  and pr_var_decl ppf vdecl =
    Stdlib.Format.fprintf ppf "%a:@ %a" Ident.pr vdecl.var_name Type.pr vdecl.var_type
  and pr_var_decl_list ppf = Util.pr_list_comma pr_var_decl ppf 
end

type expr = Expr.t

type var_decl = Expr.var_decl
      
(** Statements *)

type spec =
    { spec_form: expr;
      spec_name: string;
      spec_error: (qual_ident -> (string * string)) option;
    }

type var_decl_desc =
    { var_decl_rhs : var_decl list;
      var_decl_lhs : (expr list) option;
      var_decl_ghost : bool;
    }

type new_desc =
    { new_lhs: qual_ident;
      new_type: type_expr;
      new_args: expr list;
    }

type assign_desc =
    { assign_lhs: qual_ident;
      assign_rhs: expr;
    }

type call_desc =
    { call_lhs: qual_ident list;
      call_name: qual_ident;
      call_args: expr list;
    }

type basic_stmt_desc =
  | VarDecl of var_decl_desc 
  | New of new_desc
  | Assign of assign_desc
  | Havoc of qual_ident list
  | Call of call_desc
  | Return of expr list

type cond_desc =
    { cond_test: expr option;
      cond_then: expr;
      cond_else: expr;
    }
        
type stmt =
    { stmt_desc: stmt_desc;
      stmt_loc: location;
    }

and loop_desc =
    { loop_contract: spec list; (** the loop invariant *)
      loop_prebody: stmt; (** the statement executed before testing the loop condition *)
      loop_test: expr; (** the loop condition *)
      loop_postbody: stmt; (** the actual loop body *)
    }
      
and stmt_desc =
  | Block of stmt list
  | Basic of basic_stmt_desc
  | Loop of loop_desc
  | Cond of cond_desc


(** Functions and Procedures *)

type contract =
    { contr_name: ident; (** name of associated declaration *)
      contr_formals: ident list;  (** formal parameter list *)
      contr_returns: ident list; (** return parameter list *)
      contr_locals: var_decl ident_map; (** all local variables *)    
      contr_precond: spec list; (** precondition *)
      contr_postcond: spec list; (** postcondition *)
    }

type proc_kind =
  | Proc | Lemma | Atom

type proc_decl =
    { proc_kind: proc_kind;
      proc_contract: contract;
    }

type proc_def =
    { proc_decl: proc_decl;
      proc_body: expr option;
    }
    
type func_kind =
  | Pred | Func
      
type func_decl =
    { func_kind: func_kind;
      func_contract: contract;
    }

type func_def =
    { func_decl: func_decl;
      func_body: expr option;
    }

(* Modules *)
      
type type_alias =
    { type_alias_name: ident;
      type_alias_def: type_expr option;
      type_alias_loc: location;
    }
     
type module_decl =
    { mod_decl_name: ident;
      mod_decl_formals: ident list;
      mod_decl_returns: type_expr list;
      mod_decl_rep: ident option;
      mod_decl_mods: module_decl ident_map;
      mod_decl_types: type_alias ident_map;
      mod_decl_funcs: func_decl ident_map;
      mod_decl_procs: proc_decl ident_map;
      mod_decl_loc: location;
    }

type module_alias =
    { mod_alias_name: ident;
      mod_alias_def: type_expr;
      mod_alias_loc: location;
    }

type import_directive =
  | ModImport of type_expr
  | MemImport of qual_ident
      
type module_member_def =
  | TypeAlias of type_alias
  | Import of import_directive
  | ModDef of module_def
  | ModAlias of module_alias
  | FuncDef of func_def
  | ProcDef of proc_def
    
and module_def =
    { mod_decl: module_decl;
      mod_def: module_member_def list;
      mod_is_interface: bool;
    }
      

