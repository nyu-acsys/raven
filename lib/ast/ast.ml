(** Abstract syntax tree of a Raven program *)

open Base
open Util

type location = Loc.t

(** Identifiers *)

let print_debug _str =
  Stdio.print_endline ("\027[31m" ^ _str ^ "\027[0m");
  ()

  let print_debug2 _str =
    Stdio.print_endline ("\027[31m" ^ _str ^ "\027[0m");
    ()

module Ident = struct
  module T = struct
    type t = { ident_name : string; ident_num : int }
    [@@deriving compare, hash, sexp]

    let to_string id =
      match id.ident_num with
      | 0 -> id.ident_name
      | _ -> Printf.sprintf !"%{String}^%{Int}" id.ident_name id.ident_num
  end

  include T
  include Comparable.Make (T)

  let pr ppf id = Stdlib.Format.fprintf ppf "%s" (to_string id)
  let pr_list ppf ids = Print.pr_list_comma pr ppf ids

  let pr_ident_map pr_x ppf = 
    let open Stdlib.Format in
    let rec pr_tuple_list ppf (m : (t * 'a) list) =
      match m with
      | [] -> ()
      | (k, v) :: [] -> fprintf ppf "%a -> %a" 
        pr k
        pr_x v
      | (k, v) :: ls ->
          fprintf ppf "%a -> %a@,%a" 
          pr k
          pr_x v
          pr_tuple_list ls
      
    in

    
    (fun x ->
      let list_of_map = Map.to_alist x in
      if List.is_empty list_of_map then (fprintf ppf "_empty_map_") else
      fprintf ppf "@[<v> %a @]" pr_tuple_list (list_of_map)
  )

  let make name num = { ident_name = name; ident_num = num }
  let name id = id.ident_name

  let fresh =
    let used_names = Hashtbl.create (module String) in
    fun ?(id = 0) (name : string) ->
      let last_index =
        Hashtbl.find used_names name |> Option.value ~default:(-1)
      in
      let new_max = Int.max (last_index + 1) id in
      Hashtbl.set used_names ~key:name ~data:new_max;
      make name new_max
end

type ident = Ident.t

module IdentMap = Map.M (Ident)

type 'a ident_map = 'a IdentMap.t

(** Qualified identifiers *)

module QualIdent = struct
  module T = struct
    type t = { qual_path : Ident.t list; qual_base : Ident.t }
    [@@deriving compare, hash, sexp]
  end

  include T
  include Comparable.Make (T)

  let pr ppf qid =
    Print.pr_list_sep "." Ident.pr ppf (qid.qual_path @ [ qid.qual_base ])

  let pr_list ppf qids = Print.pr_list_comma pr ppf qids
  let to_string qid = Print.string_of_format pr qid
  let from_ident id = { qual_path = []; qual_base = id }
  let make p id = { qual_path = p; qual_base = id }

  let append qi id =
    { qual_path = qi.qual_path @ [ qi.qual_base ]; qual_base = id }
  (* append "M1.M2" "x" -> "M1.M2.x" *)

  let left_append id qi = { qi with qual_path = id :: qi.qual_path }
  (* left_append "M1" "M2.x" -> "M1.M2.x" *)

  (* { qual_path = id :: qi.qual_path; qual_base = qi.qual_base} *)
end

type qual_ident = QualIdent.t [@@deriving compare]

module QualIdentMap = Map.M (QualIdent)

type 'a qual_ident_map = 'a QualIdentMap.t


(** ----------------- *)
(** TYPES             *)
(** ----------------- *)

module Type = struct
  type type_attr = { type_loc : Loc.t [@hash.ignore] [@compare.ignore] }

  and var_decl = {
    var_name : Ident.t;
    var_loc : location; [@hash.ignore] [@compare.ignore]
    var_type : t;
    var_const : bool;
    var_ghost : bool;
    var_implicit : bool;
  }
  [@@deriving compare, hash]

  and variant_decl = {
    variant_name : Ident.t;
    variant_loc : location; [@hash.ignore] [@compare.ignore]
    variant_args : var_decl list;
  }

  (* and atomic_token =
     {
       proc : qual_ident [@compare.ignore];
       params : Stmt.var_def list;
       committed : (expr list) option;
     } *)
  and constr =
    | Int
    | Bool
    | Unit
    | Ref
    | Perm
    | Bot
    | Any
    | Var of QualIdent.t
    | Set
    | Map
    | Data of variant_decl list
    | AtomicToken

  and t = App of constr * t list * type_attr
  (* | TypeData of qual_ident * type_attr *)
  (* | Dot of t * Ident.t * type_attr *)
  [@@deriving compare, hash]

  (** Pretty printing types *)

  let ref_type_string = "Ref"
  let map_type_string = "Map"
  let set_type_string = "Set"
  let bool_type_string = "Bool"
  let int_type_string = "Int"
  let unit_type_string = "Unit"
  let perm_type_string = "Perm"
  let bot_type_string = "Bot"
  let any_type_string = "Any"
  let struct_type_string = "struct"
  let data_type_string = "struct"
  let atomic_token_type_string = "AtomicToken"

  let to_name = function
    | Int -> int_type_string
    | Bool -> bool_type_string
    | Unit -> unit_type_string
    | Bot -> bot_type_string
    | Any -> any_type_string
    | Ref -> ref_type_string
    | Set -> set_type_string
    | Map -> map_type_string
    | Perm -> perm_type_string
    | Data _ -> data_type_string
    | Var id -> QualIdent.to_string id
    | AtomicToken -> atomic_token_type_string
  (* | App _ -> "App"
     | Dot _ -> "Dot" *)

  let rec pr_constr ppf t =
    match t with
    | Int | Bool | Unit | Any | Bot | Ref | Perm | Var _ | Set | AtomicToken
    | Map ->
        Stdlib.Format.fprintf ppf "%s" (to_name t)
    | Data decls ->
        Stdlib.Format.fprintf ppf "data {@\n  @[%a@]@\n}" pr_variant_decl_list
          decls

  and pr ppf t =
    match t with
    (* | Int
       | Bool
       | Unit
       | Any
       | Bot
       | AnyRef
       | Perm
       | Var _
       | Set
       | Map ->  Stdlib.Format.fprintf ppf "%s" (to_name t)
       | Struct decls ->
           Stdlib.Format.fprintf ppf "struct {@\n  @[%a@]@\n}"
             pr_var_decl_list decls
       | Data decls ->
           Stdlib.Format.fprintf ppf "data {@\n  @[%a@]@\n}"
             pr_variant_decl_list decls *)
    | App (t1, [], _) -> pr_constr ppf t1
    | App (t1, ts, _) ->
        Stdlib.Format.fprintf ppf "%a[@[%a@]]" pr_constr t1
          (Print.pr_list_comma pr) ts

  (* | Dot (t1, id, _) ->
      Stdlib.Format.fprintf ppf "%a.%a" pr t1 Ident.pr id *)
  and pr_var_decl ppf decl =
    let open Stdlib.Format in
    fprintf ppf "%s%s @[<2>%a@ :@ %a@]"
      (if decl.var_ghost then "ghost " else "")
      (if decl.var_const then "val" else "var")
      Ident.pr decl.var_name pr decl.var_type

  and pr_var_decl_list ppf = Print.pr_list_nl pr_var_decl ppf

  and pr_variant_decl ppf decl =
    let open Stdlib.Format in
    fprintf ppf "case %a(@[%a@])" Ident.pr decl.variant_name pr_arg_list
      decl.variant_args

  and pr_variant_decl_list ppf = Print.pr_list_nl pr_variant_decl ppf

  and pr_ident ppf (id, t) =
    Stdlib.Format.fprintf ppf "%a:@ %a" Ident.pr id pr t

  and pr_arg_list ppf =
    Print.pr_list_comma
      (fun ppf decl -> pr_ident ppf (decl.var_name, decl.var_type))
      ppf

  let pr_list ppf ts = Print.pr_list_comma pr ppf ts
  let to_string t = Print.string_of_format pr t

  (** Constructors *)

  let dummy_attr = { type_loc = Loc.dummy }
  let mk_attr loc = if Loc.(loc = dummy) then dummy_attr else { type_loc = loc }
  let mk_app ?(loc = Loc.dummy) t ts = App (t, ts, mk_attr loc)
  (* let mk_dot ?(loc=Loc.dummy) t id = Dot (t, id, mk_attr loc) *)

  let mk_int loc = App (Int, [], mk_attr loc)
  let mk_bool loc = App (Bool, [], mk_attr loc)
  let mk_unit loc = App (Unit, [], mk_attr loc)
  let mk_any loc = App (Any, [], mk_attr loc)
  let mk_ref loc = App (Ref, [], mk_attr loc)
  let mk_set loc = App (Set, [], mk_attr loc)
  let mk_set_typed tp loc = App (Set, [tp], mk_attr loc)
  let mk_map loc = App (Map, [], mk_attr loc)
  let mk_perm loc = App (Perm, [], mk_attr loc)
  let mk_data decls loc = App (Data decls, [], mk_attr loc)
  let mk_var loc qid = App (Var qid, [], mk_attr loc)
  let mk_atomic_token loc = App (AtomicToken, [], mk_attr loc)


  let int = mk_int Loc.dummy
  let bool = mk_bool Loc.dummy
  let unit = mk_unit Loc.dummy
  let any = mk_any Loc.dummy

  let bot = App (Bot, [], mk_attr Loc.dummy)
  let ref = mk_ref Loc.dummy
  let set = mk_set Loc.dummy
  let set_typed tp = mk_set_typed tp Loc.dummy
  let map = mk_map Loc.dummy
  let perm = mk_perm Loc.dummy
  let data decls = mk_data decls Loc.dummy
  let var qid = mk_var Loc.dummy qid
  let atomic_token = mk_atomic_token Loc.dummy

  (* TODO: Verify join_constr properly *)

  (** Subtyping *)
  let rec join_constr t1 t2 =
    match (t1, t2) with
    | Bot, t | t, Bot -> t
    | Bool, Perm | Perm, Bool -> Perm
    (* | Ref, _
       | _, Ref -> Ref *)
    | _, _ -> Any

  (* TODO: Handle edge-cases for join properly. And figure out where and how it can be used. *)
  let rec join t1 t2 =
    if compare t1 t2 = 0 then t1 else 
    match (t1, t2) with
    | App (t1, [], a1), App (t2, [], _) -> App (join_constr t1 t2, [], a1)
    | App (Set, [t1], a1), App (Set, [t2], _a2) -> App (Set, [join t1 t2], a1)
    | App (_, _, a1), App (_, _, _) -> App (Any, [], a1)


  let rec meet_constr t1 t2 = 
    match (t1, t2) with
    | Bot, _ | _, Bot -> Bot
    | Bool, Perm | Perm, Bool -> Perm
    | Any, t | t, Any -> t
    | _, _ -> Bot


  let rec meet t1 t2 = 
    if compare t1 t2 = 0 then t1 else
    match (t1, t2) with
    | App (t1, [], a1), App (t2, [], _) -> App (meet_constr t1 t2, [], a1)
    | App (Set, [t1], a1), App (Set, [t2], _a2) -> App (Set, [meet t1 t2], a1)
    | App (_, _, a1), App (_, _, _) -> App (Bot, [], a1)
  (** Auxiliary utility functions *)
  (* TODO: Implement this properly. process_expr uses this *)

  let is_any tp_expr = (compare tp_expr (mk_any Loc.dummy)) = 0

  let is_set tp_expr = match tp_expr with
    | App (Set, _, _) -> true
    | _ -> false
  let is_ghost_var vdecl = vdecl.var_ghost
  let is_const_var vdecl = vdecl.var_const
  let is_implicit_var vdecl = vdecl.var_implicit

  let to_loc t = match t with
  | App (_, _, tp_attr) -> tp_attr.type_loc

  let equal tp1 tp2 = ((compare tp1 tp2) = 0)
end

type type_expr = Type.t [@@deriving compare]
type var_decl = Type.var_decl [@@deriving compare]


(** ----------------- *)
(** EXPRESSIONS       *)
(** ----------------- *)

module Expr = struct
  (* Does not belong here -- needs to be in the symbolic checker. *)
  (* type au_token =
     {
       proc : qual_ident [@compare.ignore];
       params : Stmt.var_def list;
       committed : (expr list) option;
     } *)

  type constr =
    (* Constants *)
    | Null
    | Unit
    | Bool of bool
    | Int of Int64.t
    | Empty
    (* Unary operators *)
    | Not
    | Uminus
    (* Binary operators *)
    | MapLookUp
    | Eq
    | Gt
    | Lt
    | Geq
    | Leq
    | Diff
    | Union
    | Inter
    | Elem
    | Subseteq
    | And
    | Or
    | Impl
    | Plus
    | Minus
    | Mult
    | Div
    | Mod
    | Dot
    | Call
    | Read
    (* Ternary operators *)
    | Ite
    | Write
    | Own
    (* Variable arity operators *)
    | Setenum
    | Var of qual_ident
    | New of type_expr [@@deriving compare]
  (* | AUToken of au_token *)

  type binder = Forall | Exists | Compr [@@deriving compare]

  type expr_attr = { expr_loc : location [@compare.ignore]; expr_type : type_expr }

  and t =
    (* Application expressions *)
    | App of constr * t list * (expr_attr [@compare.ignore])
    (* Variable binder expressions *)
    | Binder of binder * var_decl list * t * (expr_attr [@compare.ignore]) [@@deriving compare]

  let mk_attr loc t = { expr_loc = loc; expr_type = t }
  let attr_of = function App (_, _, attr) | Binder (_, _, _, attr) -> attr
  let loc t = t |> attr_of |> fun attr -> attr.expr_loc
  let to_type t = t |> attr_of |> fun attr -> attr.expr_type

  (** Pretty printing expressions *)

  let constr_to_string = function
    (* function symbols *)
    | Bool b -> Printf.sprintf "%b" b
    | Int i -> Int64.to_string i
    | Null -> "null"
    | Unit -> "()"
    | Dot -> "."
    | Call -> "call"
    | Read -> "read"
    | Write -> "write"
    | Uminus -> "-"
    | MapLookUp -> "map_lookup"
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
    | New t -> Printf.sprintf !"new %{Type}" t
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
    | Impl -> "==>"
    (* variables / uninterpreted symbols *)
    | Var id -> QualIdent.to_string id
    (* ownership predicates *)
    | Own -> "own"
    
  let pr_constr ppf c = Stdlib.Format.fprintf ppf "%s" (constr_to_string c)

  let constr_to_prio = function
    | Null | Unit | Empty | Int _ | Bool _ -> 0
    | Dot | Setenum | Read | Write | Own | Var _ | MapLookUp -> 1
    | Uminus | Not -> 2
    | Call | New _ -> 3
    | Mult | Div | Mod -> 4
    | Minus | Plus -> 5
    | Diff | Union | Inter -> 6
    | Gt | Lt | Geq | Leq | Elem | Subseteq -> 7
    | Eq -> 8
    | And -> 12
    | Or | Impl -> 16
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
    | App (And, [], a) -> pr ppf (App (Bool false, [], a))
    | App (Or, [], a) -> pr ppf (App (Bool true, [], a))
    | App ((Union | Setenum), [], a) -> pr ppf (App (Empty, [], a))
    | App (Inter, [], _) -> fprintf ppf "Univ"
    | App (c, [], _) -> fprintf ppf "%a" pr_constr c
    | App (Call, e :: es, _) -> fprintf ppf "%a(%a)" pr e pr_list es
    | App (Dot, [ e1; e2 ], _) | App (Read, [ e1; e2 ], _) ->
        fprintf ppf "(%a).(%a)" pr e1 pr e2
    | App (Write, [ e1; e2; e3 ], _) ->
        fprintf ppf "%a[|%a@ :=@ %a|]" pr e1 pr e2 pr e3
    | App
        ( (( Minus | Plus | Mult | Div | Mod | Diff | Inter | Union | Eq
           | Subseteq | Leq | Geq | Lt | Gt | Elem | And | Or | Impl ) as c),
          [ e1; e2 ],
          _ ) ->
        let pr_e1 = if constr_to_prio c < to_prio e1 then pr_paran else pr in
        let pr_e2 = if constr_to_prio c <= to_prio e2 then pr_paran else pr in
        fprintf ppf "@[<2>%a %a@ %a@]" pr_e1 e1 pr_constr c pr_e2 e2
    | App (Setenum, es, _) -> fprintf ppf "{|@[%a@]|}" pr_list es
    | App (c, es, _) -> fprintf ppf "%a(@[%a@])" pr_constr c pr_list es
    | Binder (b, vs, e1, _) ->
        fprintf ppf "@[%a@]" pr_binder (b, vs, e1, to_type e)

  and pr_list ppf = Print.pr_list_comma pr ppf
  and pr_paran ppf = Stdlib.Format.fprintf ppf "(%a)" pr

  and pr_binder ppf = function
    | ((Forall | Exists) as b), vs, e, _ ->
        Stdlib.Format.fprintf ppf "%s@ %a@ ::@ %a" (binder_to_string b)
          pr_var_decl_list vs pr e
    | Compr, vs, e, App (Set, _, _) ->
        Stdlib.Format.fprintf ppf "{|@ @[%a@ ::@ %a@]@ |}" pr_var_decl_list vs
          pr e
    | Compr, vs, e, _ ->
        Stdlib.Format.fprintf ppf "[|@ @[%a@ ::@ %a@]@ |]" pr_var_decl_list vs
          pr e

  and pr_var_decl ppf vdecl =
    let open Type in
    Stdlib.Format.fprintf ppf "%s%s%a"
      (if vdecl.var_implicit then "implicit " else "")
      (if vdecl.var_ghost then "ghost " else "")
      Type.pr_ident
      (vdecl.var_name, vdecl.var_type)

  and pr_var_decl_list ppf = Print.pr_list_comma pr_var_decl ppf

  let to_string e = Print.string_of_format pr e

  (** Constructors *)

  let mk_app ?(loc = Loc.dummy) ?(typ = Type.Any) c es =
    App (c, es, mk_attr loc (App (typ, [], Type.mk_attr loc)))

  let mk_binder ?(loc = Loc.dummy) ?(typ = Type.Any) b vs e =
    Binder (b, vs, e, mk_attr loc (App (typ, [], Type.mk_attr loc)))

  let mk_bool ?(loc = Loc.dummy) b = mk_app ~loc ~typ:Type.Bool (Bool b) []

  (** Constructor for conjunction.*)
  let mk_and ?(loc = Loc.dummy) = function
    | [] -> mk_bool ~loc false
    | [ e ] -> e
    | es ->
        let t =
          List.fold_left es ~init:(Type.mk_bool loc) ~f:(fun t e ->
              Type.join t (to_type e))
        in
        App (And, es, mk_attr loc t)

  (** Constructor for disjunction.*)
  let mk_or ?(loc = Loc.dummy) = function
    | [] -> mk_bool ~loc true
    | [ e ] -> e
    | es ->
        let t =
          List.fold_left es ~init:(Type.mk_bool loc) ~f:(fun t e ->
              Type.join t (to_type e))
        in
        App (And, es, mk_attr loc t)
end

type expr = Expr.t


(** ----------------- *)
(** STATEMENTS        *)
(** ----------------- *)

module Stmt = struct
  type spec = {
    spec_form : expr;
    spec_atomic : bool;
    spec_name : string;
    spec_error : (qual_ident -> string * string) option;
  }

  type var_def = { var_decl : var_decl; var_init : expr option }

  type new_desc = {
    new_lhs : ident;
    new_type : type_expr;
    new_args : expr list;
  }

  type assign_desc = { assign_lhs : expr list; assign_rhs : expr }

  type call_desc = {
    call_lhs : qual_ident list;
    call_name : qual_ident;
    call_args : expr list;
  }

  type fold_desc = { fold_expr : expr }
  type unfold_desc = { unfold_expr : expr }

  type basic_stmt_desc =
    | VarDef of var_def
    | Assume of spec
    | Assert of spec
    | New of new_desc
    | Assign of assign_desc
    | Havoc of expr list
    | Call of call_desc
    | Return of expr list
    | Fold of fold_desc
    | Unfold of unfold_desc
    | BindAU of ident
    | OpenAU of ident
    | AbortAU of ident
    | CommitAU of ident
    | OpenInv of expr
    | CloseInv of expr
    | Inhale of expr  
    | Exhale of expr

  type t = { stmt_desc : stmt_desc; stmt_loc : location }

  and loop_desc = {
    loop_contract : spec list;  (** the loop invariant *)
    loop_prebody : t;
        (** the statement executed before testing the loop condition *)
    loop_test : expr;  (** the loop condition *)
    loop_postbody : t;  (** the actual loop body *)
  }

  and cond_desc = { cond_test : expr; cond_then : t; cond_else : t }
  and ghost_desc = { ghost_body : t }

  and stmt_desc =
    | Block of t list
    | Basic of basic_stmt_desc
    | Loop of loop_desc
    | Cond of cond_desc
    | Ghost of ghost_desc

  (** Pretty printing statements *)

  let pr_var_def ppf vdef =
    let open Stdlib.Format in
    fprintf ppf "%s%s @[<2>%a@ :@ %a%a@]"
      (if Type.is_ghost_var vdef.var_decl then "ghost " else "")
      (if Type.is_const_var vdef.var_decl then "val" else "var")
      Ident.pr vdef.var_decl.var_name Type.pr vdef.var_decl.var_type
      (fun ppf -> function
        | Some e -> fprintf ppf "@ =@ %a" Expr.pr e
        | None -> ())
      vdef.var_init

  let rec pr_spec_list stype ppf =
    let open Stdlib.Format in
    function
    | [] -> ()
    | [ sf ] ->
        fprintf ppf "%s%s %a"
          (if sf.spec_atomic then "atomic " else "")
          stype Expr.pr sf.spec_form
    | sf :: sfs ->
        fprintf ppf "@<0>%s%s %a\n%a"
          (if sf.spec_atomic then "atomic " else "")
          stype Expr.pr sf.spec_form (pr_spec_list stype) sfs

  let pr_basic_stmt ppf =
    let open Stdlib.Format in
    function
    | VarDef vdef -> pr_var_def ppf vdef
    | Assign astm -> (
        match astm.assign_lhs with
        | [] -> Expr.pr ppf astm.assign_rhs
        | es ->
            fprintf ppf "@[<2>%a@ :=@ %a@]" Expr.pr_list es Expr.pr
              astm.assign_rhs)
    | Havoc es -> fprintf ppf "@[<2>havoc@ %a@]" Expr.pr_list es
    | New nstm -> (
        match nstm.new_args with
        | [] ->
            fprintf ppf "@[<2>%a@ :=@ new@ %a@]" Ident.pr nstm.new_lhs Type.pr
              nstm.new_type
        | args ->
            fprintf ppf "@[<2>%a@ :=@ new@ %a(%a)@]" Ident.pr nstm.new_lhs
              Type.pr nstm.new_type Expr.pr_list args)
    | Assume sf -> pr_spec_list "assume" ppf [ sf ]
    | Assert sf -> pr_spec_list "assert" ppf [ sf ]
    | Fold fld -> fprintf ppf "@[<2>fold %a@]" Expr.pr fld.fold_expr
    | Unfold ufld -> fprintf ppf "@[<2>unfold %a@]" Expr.pr ufld.unfold_expr
    | Return es -> fprintf ppf "@[<2>return@ %a@]" Expr.pr_list es
    | Call cstm -> (
        match cstm.call_lhs with
        | [] ->
            fprintf ppf "@[%a(@[%a@])@]" QualIdent.pr cstm.call_name
              Expr.pr_list cstm.call_args
        | _ ->
            fprintf ppf "@[<2>%a@ :=@ @[%a(@[%a@])@]@]" QualIdent.pr_list
              cstm.call_lhs QualIdent.pr cstm.call_name Expr.pr_list
              cstm.call_args)
    | BindAU iden -> fprintf ppf "@[<2>BindAU %a@]" Ident.pr iden
    | OpenAU open_au -> fprintf ppf "@[<2>OpenAU(%a)@]" Ident.pr open_au
    | AbortAU iden -> fprintf ppf "@[<2>AbortAU %a@]" Ident.pr iden
    | CommitAU commit_au ->
        fprintf ppf "@[<2>CommitAU %a@]" Ident.pr commit_au
    | OpenInv expr ->
      fprintf ppf "@[<2>OpenInv %a@]" Expr.pr expr
    | CloseInv expr ->
      fprintf ppf "@[<2>CloseInv %a@]" Expr.pr expr
    | Inhale expr -> fprintf ppf "@[<2>inhale %a@]" Expr.pr expr
    | Exhale expr -> fprintf ppf "@[<2>exhale %a@]" Expr.pr expr

  let rec pr ppf stmt =
    let open Stdlib.Format in
    match stmt.stmt_desc with
    | Loop ldesc ->
        fprintf ppf "%awhile (%a)@ @,@[<2>@ @ %a@]@\n%a"
          (fun ppf -> function
            | { stmt_desc = Block []; _ } -> ()
            | s -> pr ppf s)
          ldesc.loop_prebody Expr.pr ldesc.loop_test (pr_spec_list "invariant")
          ldesc.loop_contract pr ldesc.loop_postbody
    | Cond cdesc -> (
        match cdesc.cond_else.stmt_desc with
        | Block [] ->
            fprintf ppf "if (@[%a@]) %a" Expr.pr cdesc.cond_test pr
              cdesc.cond_then
        | _ ->
            fprintf ppf "if (@[%a@]) %a@ else@ %a" Expr.pr cdesc.cond_test pr
              cdesc.cond_then pr cdesc.cond_else)
    | Block stmts -> (
        match stmts with
        | [] -> fprintf ppf "{ }"
        | _ -> fprintf ppf "{@\n  @[%a@]@\n}" pr_block stmts)
    | Basic bs -> pr_basic_stmt ppf bs
    | Ghost gdesc -> fprintf ppf "{!@\n  @[%a@]@\n!}" pr gdesc.ghost_body

  and pr_block ppf stmts = Print.pr_list_nl pr ppf stmts

  let to_string s = Print.string_of_format pr s
  let print chan s = Print.print_of_format pr s chan

  (** Constructors *)

  let mk_skip loc = { stmt_desc = Block []; stmt_loc = loc }
end


(** ----------------- *)
(** CALLABLES         *)
(** ----------------- *)

module Callable = struct
  type call_kind = Proc | Lemma | Func | Pred | Invariant

  type call_decl = {
    call_decl_kind : call_kind;  (** kind of declaration *)
    call_decl_name : ident;  (** name of associated declaration *)
    call_decl_formals : ident list;  (** formal parameter list *)
    call_decl_returns : ident list;  (** return parameter list *)
    call_decl_locals : var_decl ident_map;  (** all local variables *)
    call_decl_precond : Stmt.spec list;  (** precondition *)
    call_decl_postcond : Stmt.spec list;  (** postcondition *)
    call_decl_loc : location;  (** source location of declaration *)
  }

  type proc_def = { proc_decl : call_decl; proc_body : Stmt.t option }
  type func_def = { func_decl : call_decl; func_body : expr option }

  type t = FuncDef of func_def | ProcDef of proc_def

  let pr_call_decl_specs ppf call_decl =
    let open Stdlib.Format in
    let pr_specs stype ppf = function
      | [] -> ()
      | specs -> fprintf ppf "@\n%a" (Stmt.pr_spec_list stype) specs
    in
    fprintf ppf "%a%a" (pr_specs "requires") call_decl.call_decl_precond
      (pr_specs "ensures") call_decl.call_decl_postcond

  let pr_call_decl ppf call_decl =
    let open Stdlib.Format in
    let lookup = List.map ~f:(Map.find_exn call_decl.call_decl_locals) in
    let kind =
      match call_decl.call_decl_kind with
      | Pred -> "pred"
      | Func -> "func"
      | Proc -> "proc"
      | Lemma -> "lemma"
      | Invariant -> "inv"
    in
    let pr_returns ppf = function
      | [] -> ()
      | rs ->
          fprintf ppf "@\nreturns (@[<0>%a@])" Expr.pr_var_decl_list (lookup rs)
    in
    fprintf ppf "@[<2>%s %a(@[<0>%a@])%a%a@]" 
      kind 
      Ident.pr call_decl.call_decl_name 
      (Print.pr_list_comma Expr.pr_var_decl) (lookup call_decl.call_decl_formals)
      pr_returns call_decl.call_decl_returns 
      pr_call_decl_specs call_decl

  let pr ppf def =
    let open Stdlib.Format in
    let pr_proc_body pr_body' ppf = function
      | Some e ->
          fprintf ppf "@\n@[<1> %a@]" pr_body' e
          (* Todo: make this work properly by removing the extra space.  *)
      | None -> fprintf ppf "@\n"
    in
    let pr_fn_body pr_body' ppf = function
      | Some e -> fprintf ppf "@\n{@[<1>@\n%a@]@\n}" pr_body' e
      | None -> fprintf ppf "@\n"
    in

    match def with
    | FuncDef fdef ->
        fprintf ppf "%a%a" pr_call_decl fdef.func_decl (pr_fn_body Expr.pr)
          fdef.func_body
    | ProcDef pdef ->
        fprintf ppf "%a%a" pr_call_decl pdef.proc_decl (pr_proc_body Stmt.pr)
          pdef.proc_body
end


(** ----------------- *)
(** MODULES           *)
(** ----------------- *)

module Module = struct
  type type_alias = {
    type_alias_name : ident;
    type_alias_def : type_expr option;
    type_alias_rep : bool;
    type_alias_loc : location;
  }

  type module_alias = {
    mod_alias_name : ident;
    mod_alias_type : type_expr;
    mod_alias_def : type_expr option;
    mod_alias_loc : location;
  }

  type field_def = { 
    field_name : ident; 
    field_type : type_expr; 
    field_loc : Loc.t }

  type module_decl = {
    mod_decl_name : ident;
    mod_decl_formals : ident list;
    mod_decl_returns : type_expr list; (* make this qualIdent *)
    mod_decl_rep : ident option;
    mod_decl_fields : field_def ident_map;
    mod_decl_mod_defs : module_decl ident_map;
    mod_decl_mod_aliases : module_alias ident_map;
    mod_decl_types : type_alias ident_map;
    mod_decl_callables : Callable.call_decl ident_map;
    mod_decl_vars : var_decl ident_map;
    mod_decl_loc : location;
  }

  type import_directive = ModImport of type_expr | MemImport of qual_ident

  type member_def =
    | TypeAlias of type_alias
    | Import of import_directive
    | ModDef of module_def
    | FieldDef of field_def
    | ValDef of Stmt.var_def
    | CallDef of Callable.t

  and module_def = ModImpl of t0 | ModAlias of module_alias

  and t0 = {
    mod_decl : module_decl;
    mod_def : member_def list;
    mod_interface : bool;
  }

  and sorted_member_def_list = {
    imports' : import_directive list;
    types' : type_alias list;
    fields' : field_def list;
    vars' : Stmt.var_def list;
    mod_defs' : t1 list;
    mod_aliases' : module_alias list;
    call_defs' : Callable.t list; 
  }

  and t1 = {
    module_decl' : module_decl;
    members' : sorted_member_def_list;
    interface' : bool;
  }

  and processed_member_def_list = {
    imports : import_directive list;
    types : type_alias list;
    fields : field_def list;
    vars : Stmt.var_def list;
    mod_defs : t list;
    mod_aliases : module_alias list;
    call_defs : Callable.t list; 
  }
  
  and t = {
    module_decl : module_decl;
    members : processed_member_def_list;
    interface : bool;
    obligations : processed_member_def_list;
  }

  let rec pr ppf md =
    let open Stdlib.Format in
    let mod_vs =
      List.map md.mod_decl.mod_decl_formals ~f:(fun v ->
          (v, (Map.find_exn md.mod_decl.mod_decl_mod_aliases v).mod_alias_type))
    in
    fprintf ppf "@[<2>%s@ %a%a%a@]@\n{@[<1>@\n%a@]@\n}"
      (if md.mod_interface then "interface" else "module")
      Ident.pr md.mod_decl.mod_decl_name
      (* formal parameters *)
        (fun ppf -> function
          | [] -> ()
          | vs -> fprintf ppf "[@[%a@]]" (Print.pr_list_comma Type.pr_ident) vs)
      mod_vs
      (* return types *)
        (fun ppf -> function
          | [] -> ()
          | vs -> fprintf ppf "@ : %a" Type.pr_list vs)
      md.mod_decl.mod_decl_returns (* body *) pr_member_list md.mod_def

  and pr_member ppf =
    let open Stdlib.Format in
    function
    | TypeAlias ta ->
        fprintf ppf "%stype %a%a"
          (if ta.type_alias_rep then "rep " else "")
          Ident.pr ta.type_alias_name
          (fun ppf -> function
            | None -> ()
            | Some t -> fprintf ppf " = %a" Type.pr t)
          ta.type_alias_def
    | Import (ModImport t) -> fprintf ppf "@[<2>import@ %a@]" Type.pr t
    | Import (MemImport t) -> fprintf ppf "@[<2>import@ %a@]" QualIdent.pr t
    | ModDef (ModImpl md) -> pr ppf md
    | ModDef (ModAlias ma) ->
        fprintf ppf "@[<2>module@ %a : %a%a@]" Ident.pr ma.mod_alias_name
          Type.pr ma.mod_alias_type
          (fun ppf -> function
            | None -> ()
            | Some t -> fprintf ppf " =@ %a" Type.pr t)
          ma.mod_alias_def
    | FieldDef field_def ->
        fprintf ppf "field %a: %a" Ident.pr field_def.field_name Type.pr
          field_def.field_type
    | ValDef vdef -> Stmt.pr_var_def ppf vdef
    | CallDef cdef -> Callable.pr ppf cdef

  and pr_member_list ppf ms = Print.pr_list_sep "@\n@\n" pr_member ppf ms

  and pr_import_directive ppf imp_dir = 
  let open Stdlib.Format in
  match imp_dir with
  | ModImport t -> fprintf ppf "@[<2>import@ %a@]" Type.pr t
  | MemImport t -> fprintf ppf "@[<2>import@ %a@]" QualIdent.pr t

  and pr_processed_mem_list ppf (processed_mem_list: processed_member_def_list) = 
  (let open Stdlib.Format in
  fprintf ppf "@[<v> @,%s%a @,%s%a @,%s%a @,%s%a @,%s%a @,%s%a @,%s%a @]"
  "imports: " (Print.pr_list_comma pr_import_directive) processed_mem_list.imports
  "types: " (Print.pr_list_comma pr_type_alias) processed_mem_list.types
  "fields: " (Print.pr_list_comma pr_field_decl) processed_mem_list.fields
  "vars: " (Print.pr_list_comma Stmt.pr_var_def) processed_mem_list.vars
  "mod_defs: " (Print.pr_list_comma pr_verbose) processed_mem_list.mod_defs
  "mod_aliases: " (Print.pr_list_comma pr_mod_alias) processed_mem_list.mod_aliases
  "call_defs: " (Print.pr_list_comma Callable.pr) processed_mem_list.call_defs)

  and pr_verbose ppf (md: t) =
    let open Stdlib.Format in

    fprintf ppf "@[%s%a@[@ \027[36m %a \027[0m @]@]@,{@[<1>%a@]@,}"
      (if md.interface then "interface " else "module ")
      (* module_decl *)
      Ident.pr md.module_decl.mod_decl_name
        pr_mod_decl md.module_decl
      (* body *)
        pr_processed_mem_list md.members

and pr_mod_decl ppf md = 
let open Stdlib.Format in
fprintf ppf "@[%s@[<v>@,%s%a @,%s%a @,%s%a @,%s%a @,%s%a @,%s%a @,%s%a @,%s%a @,%s%a @,%s%a @,%s @]@]@, }"
"module_decl = {"
"mod_decl_name: " Ident.pr md.mod_decl_name
"mod_decl_formals: " (Print.pr_list_comma Ident.pr) md.mod_decl_formals
"mod_decl_returns: " (Print.pr_list_comma Type.pr) md.mod_decl_returns
"mod_decl_rep: " (Print.pr_option Ident.pr) md.mod_decl_rep
"mod_decl_fields: " (Ident.pr_ident_map pr_field_decl) md.mod_decl_fields
"mod_decl_mod_defs: " (Ident.pr_ident_map Print.pr_null) md.mod_decl_mod_defs
"mod_decl_mod_aliases: " (Ident.pr_ident_map pr_mod_alias) md.mod_decl_mod_aliases
"mod_decl_types: " (Ident.pr_ident_map pr_type_alias) md.mod_decl_types
"mod_decl_callables: " (Ident.pr_ident_map Callable.pr_call_decl) md.mod_decl_callables
"mod_decl_vars: " (Ident.pr_ident_map Type.pr_var_decl) md.mod_decl_vars
"mod_decl_loc: " (* Loc.print_loc  md.mod_decl_loc *)

and pr_mod_alias ppf md_alias = 
let open Stdlib.Format in
fprintf ppf "@[%s @[<v> @,%s%a @,%s%a @,%s%a @,%s @] @,}@]"
"module_alias = {"
"mod_alias_name: " Ident.pr md_alias.mod_alias_name
"mod_alias_type: " Type.pr md_alias.mod_alias_type
"mod_alias_def: " (Print.pr_option Type.pr) md_alias.mod_alias_def
"mod_alias_loc: " (* Loc.print_loc  md.mod_decl_loc *)

and pr_type_alias ppf tp_alias =
let open Stdlib.Format in
fprintf ppf "@[%s@[<v>@,%s%a @,%s%a @,%s%B @,%s@]@,}@]"
"type_alias = {" 
"type_alias_name: " Ident.pr tp_alias.type_alias_name
"type_alias_def: " (Print.pr_option Type.pr) tp_alias.type_alias_def
"type_alias_rep: " tp_alias.type_alias_rep
"type_alias_loc: " (*Loc.print_loc  md.mod_decl_loc*)

and pr_field_decl ppf field_decl =
let open Stdlib.Format in
fprintf ppf "@[<1> %s @[<v> @,%s%a @,%s%a @,%s @] @,}@]"
"field_decl = {" 
"field_name: " Ident.pr field_decl.field_name
"field_type: " Type.pr field_decl.field_type
"field_loc: " (* Loc.print_loc  field_decl.field_loc *)

  let to_string m = Print.string_of_format pr m
  let print chan m = Print.print_of_format pr m chan
  let print_verbose chan m = Print.print_of_format pr_verbose m chan
  let print_member_list chan ms = Print.print_of_format pr_member_list ms chan

  (** Constructors *)

  let empty_decl =
    {
      mod_decl_name = Ident.make "" 0;
      mod_decl_formals = [];
      mod_decl_returns = [];
      mod_decl_fields = Base.Map.empty (module Ident);
      mod_decl_rep = None;
      mod_decl_mod_defs = Base.Map.empty (module Ident);
      mod_decl_mod_aliases = Base.Map.empty (module Ident);
      mod_decl_types = Base.Map.empty (module Ident);
      mod_decl_callables = Base.Map.empty (module Ident);
      mod_decl_vars = Base.Map.empty (module Ident);
      mod_decl_loc = Loc.dummy;
    }

  let empty_sorted_member_def_list = {
    imports' = [];
    types' = [];
    fields' = [];
    vars' = [];
    mod_defs' = [];
    mod_aliases' = [];
    call_defs' = [];
  }

  let empty_processed_member_def_list = {
    imports = [];
    types = [];
    fields = [];
    vars = [];
    mod_defs = [];
    mod_aliases = [];
    call_defs = [];
  }
end

module ASTUtil = struct
  let expr_to_qual_ident (expr : expr) =
    match expr with
    | App (Var qual_ident, [], _) -> qual_ident
    | App (Var _, _, _) -> raise (Failure "Var expr should not have arguments.")
    | _ ->
        Error.error_simple (*(Expr.loc expr)*)
             (Printf.sprintf "Expected Var expression instead of %s; Loc: %s" (Expr.to_string expr) (Loc.to_string (Expr.loc expr)))

  let qual_ident_to_expr (qual_ident: qual_ident) (expr_attr: Expr.expr_attr): expr = 
    App (Var qual_ident, [], expr_attr)

  let qual_ident_to_ident (qual_ident : qual_ident) =
    if List.is_empty qual_ident.qual_path then qual_ident.qual_base
    else raise (Failure "Var expr should be unqualified var.")

  let expr_to_ident (expr : expr) =
    qual_ident_to_ident (expr_to_qual_ident expr)

  let type_expr_to_qual_ident (type_expr: type_expr) =
    match type_expr with
    | App (constr, _tp_expr_list, type_attr) ->
      match constr with
      | Var qual_ident -> qual_ident
      | _ -> Error.error type_attr.type_loc "Expected type_expr to be qualIdent"
end