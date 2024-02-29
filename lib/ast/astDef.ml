(** Definition of abstract syntax tree of a Raven program *)

open Base
open Util

type location = Loc.t

(** Identifiers *)

module Ident = struct
  module T = struct
    type t = { ident_name : string; ident_num : int; ident_loc : Loc.t [@compare.ignore] [@hash.ignore] }
    [@@deriving compare, hash, sexp]

    let to_string id =
      match id.ident_num with
      | 0 -> id.ident_name
      | _ -> Printf.sprintf !"%{String}^%{Int}" id.ident_name id.ident_num

    let to_loc id = id.ident_loc      
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

  let make loc name num = { ident_name = name; ident_num = num; ident_loc = loc }
  let name id = id.ident_name

  let used_names = Hashtbl.create (module String)

  let fresh loc =
    
    fun ?(id = 0) (name : string) ->
      let last_index =
        Hashtbl.find used_names name |> Option.value ~default:(-1)
      in
      let new_max = Int.max (last_index + 1) id in
      Logs.debug (fun m -> m "Keyset: %d" (List.count (Hashtbl.keys used_names) ~f:(fun _ -> true)));
      Logs.debug (fun m -> m "old id %s -> %d" name last_index);
      Logs.debug (fun m -> m "fresh id %s -> %d" name new_max);
      Hashtbl.set used_names ~key:name ~data:new_max;
      make loc name new_max
end

type ident = Ident.t

module IdentSet = Set.M (Ident)

module IdentMap = Map.M (Ident)

type 'a ident_map = 'a IdentMap.t

module IdentHashtbl = Hashtbl.M (Ident)

type 'a ident_hashtbl = 'a IdentHashtbl.t

(** Qualified identifiers *)

module QualIdent = struct
  (* CAUTION: the implementation uses hash consing to get unique in-memory representations of qualified identifiers.
     Only use the function QualIdent.make for constructing values of type QualIdent.t. Do not create new values directly!! *)
  
  module T = struct
    type t = {
      qual_unique_id : int;
      qual_path : Ident.t list; [@hash.ignore] [@compare.ignore]
      qual_base : Ident.t [@hash.ignore] [@compare.ignore]
    }
    [@@deriving compare, hash, sexp]
  end

  include T
  include Comparable.Make (T)

  (* Substitution maps for module instantiation *)
  type subst = (t * Ident.t list) list

  let to_loc qid = Ident.to_loc qid.qual_base
  
  let to_list qid =
    qid.qual_path @ [ qid.qual_base ]

  let to_rev_list qid =
    qid.qual_base :: List.rev qid.qual_path

  let first_ident qid =
    match qid.qual_path with
    | id :: _ -> id
    | [] -> qid.qual_base
      
  let pr ppf qid =
    Print.pr_list_sep "." Ident.pr ppf (to_list qid)

  let pr_list ppf qids = Print.pr_list_comma pr ppf qids

  let to_string qid = Print.string_of_format pr qid

  let to_ident qid =
    match qid.qual_path with
    | [] -> qid.qual_base
    | _ -> failwith (Printf.sprintf "qualified ident %s should be unqualified." (to_string qid))

  let unqualify qid = qid.qual_base

  let is_local qid = List.is_empty qid.qual_path

  let is_qualified qid = not @@ is_local qid
  
  module IdentList = struct
    type t = Ident.t list [@@deriving hash, compare, sexp]
  end

  (** [make p id] creates a qualified identifier with path [p] and base [id].
      Only use this function to construct values of type QualIdent.t *)
  let make =
    let counter = ref 0 in
    let existing_ids = Hashtbl.create (module IdentList) in
    fun p id ->
      Hashtbl.find existing_ids (id :: p) |>
      Option.map ~f:(fun unique_id -> { qual_unique_id = unique_id; qual_path = p; qual_base = id }) |>
      Option.lazy_value ~default:(fun () ->
          let uid = !counter in
          let _ = Stdlib.incr counter in
          let qual_ident = { qual_unique_id = uid; qual_path = p; qual_base = id } in
          let _ = Hashtbl.add_exn existing_ids ~key:(id :: p) ~data:uid in
          qual_ident)


  let from_rev_list = function
    | id :: p -> make (List.rev p) id
    | _ -> failwith "empty list"
    
  let from_list ids = from_rev_list (List.rev ids)
  
  let from_ident id = make [] id

  let path qid = qid.qual_path
  
  (* append "M1.M2" "x" -> "M1.M2.x" *)
  let append qi id = make (qi.qual_path @ [ qi.qual_base ]) id

  (* left_append "M1" "M2.x" -> "M1.M2.x" *)
  let left_append id qi = make (id :: qi.qual_path) qi.qual_base

  (* concat "qid1" "qid2" -> "qid1.quid2" *)
  let concat qid1 qid2 = make (qid1.qual_path @ qid1.qual_base :: qid2.qual_path) qid2.qual_base

  let pop qid = match qid.qual_path with
    | [] -> failwith "Cannot pop from empty path"
    | path -> make (List.drop_last_exn path) (List.last_exn path)


  let requalify_path subst path = 
    let f path (p, p_new) =
      let rec requalify p1 p2 =
        match p1, p2 with
        | [], p2 -> List.append p_new p2
        | id1 :: p1, id2 :: p2 when Ident.(id1 = id2) ->
          requalify p1 p2
        | _ -> path
      in
      requalify (to_list p) path
    in
    List.fold_left subst ~init:path ~f
  
  (* requalify [(p, p_new)] "p.p2.x" -> "p_new.p2.x" *)
  let requalify subst qid =
    let path = requalify_path subst (to_list qid) in
    from_list path
end

type qual_ident = QualIdent.t [@@deriving compare]

module QualIdentSet = Set.M (QualIdent)

module QualIdentMap = Map.M (QualIdent)

module QualIdentHashtbl = Hashtbl.M (QualIdent)

type 'a qual_ident_map = 'a QualIdentMap.t

type 'a qual_ident_hashtbl = 'a QualIdentHashtbl.t



(** Types *)

module Type = struct
  module T = struct
    type type_attr = { type_loc : Loc.t [@hash.ignore] [@compare.ignore] }

    and var_decl = {
      var_name : Ident.t;
      var_loc : Loc.t; [@hash.ignore] [@compare.ignore]
      var_type : t;
      var_const : bool;
      var_ghost : bool;
      var_implicit : bool;
    }
    [@@deriving compare, hash, sexp]

    and variant_decl = {
      variant_name : Ident.t;
      variant_loc : Loc.t; [@hash.ignore] [@compare.ignore]
      variant_args : var_decl list;
    }

    and constr =
      | Int
      | Real
      | Num
      | Bool
      | Ref
      | Perm
      | Bot
      | Any
      | Var of QualIdent.t
      | Set
      | Map
      | Fld
      | Data of QualIdent.t * variant_decl list
      | AtomicToken
      | Prod

    and t = App of constr * t list * type_attr
    [@@deriving compare, hash, sexp]
  end

  include T
  include Comparable.Make (T)
    
  let attr_of = function App (_, _, attr) -> attr
  let loc t = t |> attr_of |> fun attr -> attr.type_loc


  (** Pretty printing types *)

  let ref_type_string = "Ref"
  let map_type_string = "Map"
  let set_type_string = "Set"
  let fld_type_string = "Fld"
  let bool_type_string = "Bool"
  let int_type_string = "Int"
  let real_type_string = "Real"
  let num_type_string = "Int or Real"
  let perm_type_string = "Perm"
  let bot_type_string = "Bot"
  let any_type_string = "Any"
  let data_type_string = "struct"
  let atomic_token_type_string = "AtomicToken"
  let prod_type_string = "Prod"

  let to_name = function
    | Int -> int_type_string
    | Real -> real_type_string
    | Num -> num_type_string
    | Bool -> bool_type_string
    | Bot -> bot_type_string
    | Any -> any_type_string
    | Ref -> ref_type_string
    | Set -> set_type_string
    | Map -> map_type_string
    | Fld -> fld_type_string
    | Perm -> perm_type_string
    | Data (id, _) -> QualIdent.to_string id
    | Var id -> QualIdent.to_string id
    | AtomicToken -> atomic_token_type_string
    | Prod -> prod_type_string

  let rec pr_constr ppf t =
    match t with
    | Int | Real | Num | Bool | Any | Bot | Ref | Perm | Var _ | Set | AtomicToken
    | Map | Fld | Prod ->
        Stdlib.Format.fprintf ppf "%s" (to_name t)
    | Data (id, decls) ->
      Stdlib.Format.fprintf ppf "data %a {@\n  @[<2>%a@]@\n}"
        QualIdent.pr id
        pr_variant_decl_list decls

  and pr ppf t =
    match t with
    | App (t1, [], _) -> pr_constr ppf t1
    | App (Prod, ts, _) ->
      Stdlib.Format.fprintf ppf "(@[%a@])" (Print.pr_list_comma pr) ts
    | App (t1, ts, _) ->
        Stdlib.Format.fprintf ppf "%a[@[%a@]]" pr_constr t1
          (Print.pr_list_comma pr) ts

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

  and pr_variant_decl_list ppf variant_decl_list = 
    Print.pr_list_nl pr_variant_decl ppf variant_decl_list
    (* Stdlib.Format.fprintf ppf "" *)


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

  let mk_int loc = App (Int, [], mk_attr loc)
  let mk_real loc = App (Real, [], mk_attr loc)
  let mk_num loc = App (Num, [], mk_attr loc)
  let mk_bool loc = App (Bool, [], mk_attr loc)
  let mk_unit loc = App (Prod, [], mk_attr loc)
  let mk_any loc = App (Any, [], mk_attr loc)
  let mk_bot loc = App (Bot, [], mk_attr loc)
  let mk_ref loc = App (Ref, [], mk_attr loc)
  let mk_set loc tp = App (Set, [tp], mk_attr loc)
  let mk_map loc tpi tpo = App (Map, [tpi; tpo], mk_attr loc)
  let mk_fld loc tpf = App (Fld, [tpf], mk_attr loc)
  let mk_perm loc = App (Perm, [], mk_attr loc)
  let mk_data id decls loc = App (Data (id, decls), [], mk_attr loc)
  let mk_var loc qid = App (Var qid, [], mk_attr loc)
  let mk_atomic_token loc = App (AtomicToken, [], mk_attr loc)
  let mk_prod loc tp_list = 
    match tp_list with
    | [] -> mk_unit loc
    | tp :: [] -> tp
    | _ -> App (Prod, tp_list, mk_attr loc)


  let int = mk_int Loc.dummy
  let real = mk_real Loc.dummy
  let num = mk_num Loc.dummy
  let bool = mk_bool Loc.dummy
  let unit = mk_unit Loc.dummy
  let any = mk_any Loc.dummy
  let bot = mk_bot Loc.dummy
  let ref = mk_ref Loc.dummy
  let set = mk_set Loc.dummy bot
  let set_typed tp = mk_set Loc.dummy tp
  let map = mk_map Loc.dummy
  let perm = mk_perm Loc.dummy
  let data id decls = mk_data id decls Loc.dummy
  let var qid = mk_var Loc.dummy qid
  let atomic_token = mk_atomic_token Loc.dummy

  (** Equality and Subtyping *)

  (*let equal tp1 tp2 = ((compare tp1 tp2) = 0)*)
      
  let rec join_constr (t1: constr) t2 =
    if Poly.(t1 = t2) then t1 else
    match t1, t2 with
    | Bot, t | t, Bot -> t
    | Bool, Perm | Perm, Bool -> Perm
    | (Int | Real | Num), (Int | Real | Num) when not @@ Poly.(t1 = t2) -> Num
    | _, _ -> Any
 
  let rec meet_constr t1 t2 = 
    if Poly.(t1 = t2) then t1 else
    match t1, t2 with
    | Any, t | t, Any -> t
    | Bool, Perm | Perm, Bool -> Bool
    | Int, Num | Num, Int -> Int
    | Real, Num | Num, Real -> Real
    | _, _ -> Bot

  let rec join t1 t2 =
    if equal t1 t2 then t1 else 
    match (t1, t2) with
    | App (Bot, [], _), t | t, App (Bot, [], _) -> t
    | App (t1, [], a1), App (t2, [], _) -> App (join_constr t1 t2, [], a1)
    | App (Set, [t1], a1), App (Set, [t2], _a2) -> App (Set, [join t1 t2], a1)
    | App (Map, [ti1; to1], a1), App (Map, [ti2; to2], _) -> App (Any, [meet ti1 ti2; join to1 to2], a1)
    | App (Prod, ts1, a1), App (Prod, ts2, _a2) ->
      (List.map2 ~f:join ts1 ts2 |> function
      | Ok ts -> App (Prod, ts, a1)
      | _ -> App (Any, [], a1))
    | App (Fld, [tf1], _), App (Fld, [tf2], _) when equal tf1 tf2 -> t1 
    | App (_, _, a1), App (_, _, _) -> App (Any, [], a1)

  and meet t1 t2 = 
    if equal t1 t2 then t1 else
    match (t1, t2) with
    | App (Any, [], _), t | t, App (Any, [], _) -> t
    | App (t1, [], a1), App (t2, [], _) -> App (meet_constr t1 t2, [], a1)
    | App (Set, [t1], a1), App (Set, [t2], _a2) -> App (Set, [meet t1 t2], a1)
    | App (Map, [ti1; to1], a1), App (Map, [ti2; to2], _) -> App (Map, [join ti1 ti2; meet to1 to2], a1)
    | App (Prod, ts1, a1), App (Prod, ts2, _a2) ->
      (List.map2 ~f:meet ts1 ts2 |> function
      | Ok ts -> App (Prod, ts, a1)
      | _ -> App (Bot, [], a1))      
    | App (Fld, [tf1], _), App (Fld, [tf2], _) when equal tf1 tf2 -> t1 
    | App (_, _, a1), App (_, _, _) -> App (Bot, [], a1)

  let subtype_of tp1 tp2 = equal (join tp1 tp2) tp2
          
  (** Auxiliary utility functions *)
  
  let mk_var_decl ?(loc = Loc.dummy) ?(const = false) ?(ghost = false) ?(implicit = false) name tp =
    { var_name = name; var_loc = loc; var_type = tp; var_const = const; var_ghost = ghost; var_implicit = implicit }

  let is_num tp =
    equal tp real || equal tp int

  let is_any tp_expr = equal tp_expr any

  let is_set tp_expr = match tp_expr with
    | App (Set, _, _) -> true
    | _ -> false
  let is_ghost_var vdecl = vdecl.var_ghost
  let is_const_var vdecl = vdecl.var_const
  let is_implicit_var vdecl = vdecl.var_implicit

  let to_loc t = match t with
  | App (_, _, tp_attr) -> tp_attr.type_loc

  let to_qual_ident_exn t =
    match t with
    | App (constr, _tp_expr_list, type_attr) ->
      match constr with
      | Var qual_ident -> qual_ident
      | _ -> Error.error type_attr.type_loc "Expected type variable"

  
  let set_elem = function
  | App (Set, elem :: _, _) -> elem
  | _ -> failwith "Expected Set type"
        
  let map_dom = function
  | App (Map, dom :: _, _) -> dom
  | _t -> failwith ("Expected Map type; found: " ^ (to_string _t))
        
  let map_codom = function
  | App (Map, _ :: codom :: _, _) -> codom
  | _t -> failwith ("Expected Map type; found: " ^ (to_string _t))

  let tuple_lookup tp i = 
    match tp with
    | App (Prod, ts, _) -> 
      begin match List.nth ts i with
      | Some t -> t
      | None -> failwith "Index out of bounds"
      end
    | _ -> failwith "Expected Tuple type"

  let symbols ?(acc = Set.empty (module QualIdent)) tp =
    let rec symbols acc = function
      | App (c, ts, _) ->
        let acc = match c with
          | Var id -> Set.add acc id
          | Data (id, variant_decls) ->
            let acc = Set.add acc id in
            let var_args = List.concat_map ~f:(fun vdecl -> vdecl.variant_args) variant_decls in
            List.fold var_args ~init:acc ~f:(fun acc v_arg -> symbols acc v_arg.var_type) 
          | _ -> acc
        in
        List.fold ~init:acc ~f:symbols ts
    in
    symbols acc tp
end

type type_expr = Type.t [@@deriving compare]
type var_decl = Type.var_decl [@@deriving compare]


(** Expressions *)

module Expr = struct

  type constr =
    (* Constants *)
    | Null
    (* | Unit <- obsolete (use empty tuple) *)
    | Bool of bool
    | Int of Int64.t
    | Real of Float.t
    | Empty
    (* Unary operators *)
    | Not
    | Uminus
    (* Binary operators *)
    | TupleLookUp
    | MapLookUp
    | MapUpdate
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
    (*| Call of qual_ident * (location [@compare.ignore])*)
    | DataConstr of QualIdent.t
    | DataDestr of QualIdent.t
    | Read
    (* Ternary operators *)
    | Ite
    | Own
    (* Variable arity operators *)
    | Setenum
    | Tuple
    | Var of QualIdent.t [@@deriving compare, equal]
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
  let to_loc t = t |> attr_of |> fun attr -> attr.expr_loc
  let to_type t = t |> attr_of |> fun attr -> attr.expr_type

  let set_type t tp = 
    let attr = attr_of t in
    let attr = { attr with expr_type = tp } in
    match t with 
    | App (constr, expr_list, _expr_attr) -> App (constr, expr_list, attr)
    | Binder (b, v_l, expr, _expr_attr) -> Binder (b, v_l, expr, attr)

  (** Pretty printing expressions *)

  let constr_to_string = function
    (* function symbols *)
    | Bool b -> Printf.sprintf "%b" b
    | Int i -> Int64.to_string i
    | Real r -> Float.to_string r
    | Null -> "null"
    | Tuple -> "()"
    | DataConstr id
    | DataDestr id -> QualIdent.to_string id
    (*| Call (id, _) -> "call " ^ QualIdent.to_string id*)
    | Read -> "read"
    | Uminus -> "-"
    | TupleLookUp -> "tuple_lookup"
    | MapLookUp -> "map_lookup"
    | MapUpdate -> "map_update"
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
    | Impl -> "==>"
    (* variables / uninterpreted symbols *)
    | Var id -> QualIdent.to_string id
    (* ownership predicates *)
    | Own -> "own"
    
  let pr_constr ppf c = Stdlib.Format.fprintf ppf "%s" (constr_to_string c)

  let constr_to_prio = function
    | Null | Empty | Int _ | Real _ | Bool _ -> 0
    | Setenum | Tuple | Read | Own | Var _ | TupleLookUp | MapLookUp | MapUpdate -> 1
    | Uminus | Not -> 2
    | DataConstr _ | DataDestr _ -> 3
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

  (* The first pr is a more verbose print which prints types of each expression. This is useful for debugging. The second pr is the normal pr which is prettier. *)
  let rec pr_verbose ppf e =
    let open Stdlib.Format in
    match e with
    | App (And, [], a) -> pr ppf (App (Bool false, [], a))
    | App (Or, [], a) -> pr ppf (App (Bool true, [], a))
    | App ((Union | Setenum), [], a) -> pr ppf (App (Empty, [], a))
    | App (Inter, [], _) -> fprintf ppf "Univ"
    | App (c, [], _) -> fprintf ppf "(%a \027[35m :%a \027[0m)" pr_constr c Type.pr (to_type e)
    | App (DataConstr id, es, _) | App (Var id, (( _ :: _ ) as es), _) ->
        fprintf ppf "(%a(%a) \027[35m :%a \027[0m)" QualIdent.pr id pr_list es Type.pr (to_type e)
    | App (Read, [ e1; e2 ], _) ->
        fprintf ppf "((%a).(%a) \027[35m :%a \027[0m)" pr e1 pr e2 Type.pr (to_type e)
    | App (MapLookUp, [e1; e2], _) ->
        fprintf ppf "(%a[%a@] \027[35m :%a \027[0m)" pr e1 pr e2 Type.pr (to_type e)
    | App (MapUpdate, [ e1; e2; e3 ], _) ->
        fprintf ppf "(%a[%a@ :=@ %a] \027[35m :%a \027[0m)" pr e1 pr e2 pr e3 Type.pr (to_type e)
    | App
        ( (( Minus | Plus | Mult | Div | Mod | Diff | Inter | Union | Eq
           | Subseteq | Leq | Geq | Lt | Gt | Elem | And | Or | Impl ) as c),
          [ e1; e2 ],
          _ ) ->
        let pr_e1 = if constr_to_prio c < to_prio e1 then pr_paran else pr in
        let pr_e2 = if constr_to_prio c <= to_prio e2 then pr_paran else pr in
        fprintf ppf "@[<2>(%a %a@ %a \027[35m :%a \027[0m)@]" pr_e1 e1 pr_constr c pr_e2 e2 Type.pr (to_type e)
    | App (Setenum, es, _) -> fprintf ppf "({|@[%a@]|} \027[35m :%a \027[0m)" pr_list es Type.pr (to_type e)
    | App (Tuple, es, _) -> fprintf ppf "(@[<1>%a@])" pr_list es
    | App (c, es, _) -> fprintf ppf "(%a(@[%a@]) \027[35m :%a \027[0m)" pr_constr c pr_list es Type.pr (to_type e)
    | Binder (b, vs, e1, _) ->
        fprintf ppf "@[(%a \027[35m :%a \027[0m)@]" pr_binder (b, vs, e1, to_type e) Type.pr (to_type e)


  and pr_compact ppf e =
    let open Stdlib.Format in
    match e with
    | App (And, [], a) -> pr ppf (App (Bool false, [], a))
    | App (Or, [], a) -> pr ppf (App (Bool true, [], a))
    | App ((Union | Setenum), [], a) -> pr ppf (App (Empty, [], a))
    | App (Inter, [], _) -> fprintf ppf "Univ"
    | App (c, [], _) -> fprintf ppf "%a" pr_constr c
    | App (DataConstr id, es, _) | App (Var id, ((_ :: _) as es), _) ->
      fprintf ppf "%a(%a)" QualIdent.pr id pr_list_compact es
    | App
        ( (( Minus | Plus | Mult | Div | Mod | Diff | Inter | Union | Eq
           | Subseteq | Leq | Geq | Lt | Gt | Elem | And | Or | Impl ) as c),
          [ e1; e2 ],
          _ ) ->
        let pr_e1 = if constr_to_prio c < to_prio e1 then pr_paran else pr in
        let pr_e2 = if constr_to_prio c <= to_prio e2 then pr_paran else pr in
        fprintf ppf "%a %a@ %a" pr_e1 e1 pr_constr c pr_e2 e2
    | App (Setenum, es, _) -> fprintf ppf "{|%a|}" pr_list_compact es
    | App (Tuple, es, _) -> fprintf ppf "(@[<1>%a@])" pr_list_compact es
    | App (c, es, _) -> fprintf ppf "%a(%a)" pr_constr c pr_list_compact es
    | Binder (b, vs, e1, _) ->
        fprintf ppf "%a" pr_binder (b, vs, e1, to_type e)

  and pr ppf e = pr_compact ppf e
  (* and pr ppf e = pr_verbose ppf e *)

  and pr_list ppf = Print.pr_list_comma pr ppf

  and pr_list_compact ppf = Print.pr_list_comma pr_compact ppf
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
  
  let mk_app ?(loc = Loc.dummy) ?(typ = Type.bot) c es =
    App (c, es, mk_attr loc typ)

  let mk_var ?(loc = Loc.dummy) ~typ (qual_ident: qual_ident) = 
    mk_app ~loc ~typ (Var qual_ident) []

  let mk_binder ?(loc = Loc.dummy) ?(typ = Type.bool) b vs e =
    match vs with 
    | [] -> e
    | _ -> Binder (b, vs, e, mk_attr loc typ)

  let mk_bool ?(loc = Loc.dummy) b = mk_app ~loc ~typ:Type.bool (Bool b) []

  let mk_tuple ?(loc = Loc.dummy) es = 
    match es with
    | e :: [] -> e
    | _ -> mk_app ~loc ~typ:(Type.mk_prod loc (List.map es ~f:to_type)) Tuple es

  let mk_unit loc = mk_tuple ~loc []
  
  (** Constructor for conjunction.*)
  let mk_and ?(loc = Loc.dummy) = function
    | [] -> mk_bool ~loc true
    | [ e ] -> e
    | es ->
        let t =
          List.fold_left es ~init:(Type.mk_bool loc) ~f:(fun t e ->
              Type.join t (to_type e))
        in
        App (And, es, mk_attr loc t)

  (** Constructor for disjunction.*)
  let mk_or ?(loc = Loc.dummy) = function
    | [] -> mk_bool ~loc false
    | [ e ] -> e
    | es ->
        let t =
          List.fold_left es ~init:(Type.mk_bool loc) ~f:(fun t e ->
              Type.join t (to_type e))
        in
        App (And, es, mk_attr loc t)

  let mk_not ?(loc = Loc.dummy) e =
    (* let t = to_type e in *)
    App (Not, [ e ], mk_attr loc Type.bool)


  let mk_eq ?(loc = Loc.dummy) e1 e2 =
    let typ_join = (Type.join (to_type e1) (to_type e2)) in
    assert (  Type.equal typ_join (to_type e1)  || Type.equal typ_join (to_type e2)  );
    (* let t = Type.join (to_type e1) (to_type e2) in *)
    App (Eq, [ e1; e2 ], mk_attr loc Type.bool)

  let mk_impl ?(loc = Loc.dummy) e1 e2 =
    assert (Type.equal (to_type e1) Type.bool);
    (assert ((Type.equal (to_type e2) Type.bool) || (Type.equal (to_type e2) Type.perm)));

    App (Impl, [ e1; e2 ], mk_attr loc (Type.join (to_type e1) (to_type e2)))

  let mk_maplookup ?(loc = Loc.dummy) e1 e2 =
    let t = Type.map_codom (to_type e1) in
    App (MapLookUp, [ e1; e2 ], mk_attr loc t)
  
  let from_var_decl (var_decl:var_decl) =
    mk_var ~loc:var_decl.var_loc ~typ:var_decl.var_type (QualIdent.from_ident var_decl.var_name)

  (** Auxiliary functions *)

  let to_qual_ident expr =
    match expr with
    | App (Var qual_ident, _, _) -> qual_ident
    | _ ->
      Error.error (to_loc expr)
        (Printf.sprintf "Expected Var expression instead of %s" (to_string expr))

  let to_ident expr =
    expr |> to_qual_ident |> QualIdent.to_ident

  let is_ident expr =
    match expr with
    | App (Var qual_ident, [], _) -> QualIdent.is_local qual_ident
    | _ -> false

  let to_int expr = 
    match expr with
    | App (Int i, _, _) -> Int.of_int64_exn i
    | _ -> Error.error (to_loc expr) "Expected Int expression"

  (** Map all identifiers occuring in expression [e] to new identifiers according to function [fct] *)
  let map_idents fct e =
  let rec sub = function
    | App (constr, args, expr_attr) ->
      let args = List.map args ~f:sub in
      let constr =
        match constr with
        | Var qual_ident -> Var (fct qual_ident)
        | DataConstr qual_ident -> DataConstr (fct qual_ident)
        | DataDestr qual_ident -> DataDestr (fct qual_ident)
        | _ -> constr
      in
      App (constr, args, expr_attr)
    | Binder (b, vars, e, expr_attr) ->
      Binder (b, vars, sub e, expr_attr)
  in sub e
    
  (** Substitutes all identifiers in expression [e] with other identifiers according to substitution map [subst_map].
   ** This operation is not capture avoiding. *)
  let subst_idents subst_map e =
    let sub_id id =
      Map.find subst_map id |> Option.value ~default:id
    in
    map_idents sub_id e

  (** Equality test on expressions. Compares expressions modulo alpha renaming, 
   * stripping off annotations, etc. *)
  let alpha_equal ?(sm = Map.empty (module QualIdent)) e1 e2 =
  (* The map sm represents a bijection between the bound variables in e2 and e1. *)
  let rec eq sm e1 e2 =
    match e1, e2 with         
    | App (constr1, es1, _), App (constr2, es2, _) ->
      let b =
        match constr1, constr2 with
        | Var qual_ident1, Var qual_ident2 ->
          let qual_ident2p =
            Map.find sm qual_ident2 |> Option.value ~default:qual_ident2
          in
          QualIdent.(qual_ident1 = qual_ident2p)
        | _ -> equal_constr constr1 constr2
      in
      b && List.for_all2 es1 es2 ~f:(eq sm) |> (function Ok b -> b | Unequal_lengths -> false)
    | Binder (b1, vs1, e1, _), Binder (b2, vs2, e2, _)
      when Poly.(b1 = b2) ->
      let sm = List.fold2 vs1 vs2 ~init:sm ~f:(fun sm var_decl1 var_decl2 ->
          let var1 = QualIdent.from_ident var_decl1.Type.var_name in
          let var2 = QualIdent.from_ident var_decl2.Type.var_name in
          Map.set sm ~key:var2 ~data:var1)
      in
      begin match sm with
      | Ok sm -> eq sm e1 e2
      | Unequal_lengths -> false
      end
    | _ -> false
  in
  eq sm e1 e2

  
  let rec alpha_renaming (expr: t) (map: t qual_ident_map) : t =
  match expr with
  | App (constr, expr_list, expr_attr) ->
    let expr_list = List.map expr_list ~f:(fun expr -> alpha_renaming expr map) in

    (match constr with
    | Var qual_ident ->
      (match Map.find map qual_ident with
      | None ->
        App (Var qual_ident, expr_list, expr_attr)
      | Some expr' ->
        (* TODO: Potentially dropping expr_list here *)
        expr'
      )
    | _ -> App (constr, expr_list, expr_attr)

    )

  | Binder (binder, var_decl_list, expr, expr_attr) ->
    (* TODO: Rename the var_decl to avoid clashing with variables in the map *)
    let expr = alpha_renaming expr map in
    Binder (binder, var_decl_list, expr, expr_attr)

  (** Extends [acc] with the signature of the free variables occuring in expression [e]. *)
  let signature ?(acc = Map.empty (module QualIdent)) e = 
    let rec fv bv vars = function
      | App (Var id, [],  attr) -> 
        if Set.mem bv id
        then vars
        else Map.set vars ~key:id ~data:attr.expr_type
      | App (_, ts, _) ->
	List.fold_left ts ~f:(fv bv) ~init:vars
      | Binder (_, vs, e, _) ->
        let bv =
          List.fold_left vs
            ~init:bv ~f:(fun bv var_decl -> Set.add bv (QualIdent.from_ident var_decl.var_name))
        in
        fv bv vars e
    in 
    fv (Set.empty (module QualIdent)) acc e 
  
  (** Extends [acc] with the set of all symbols occuring free in expression [e]. *)
  let symbols ?(acc = Set.empty (module QualIdent)) e = 
    let rec symbols bv syms = function
      | App (Var id, ts,  attr) -> 
        let syms = List.fold_left ts ~f:(symbols bv) ~init:syms in
        if Set.mem bv id
        then syms
        else Set.add syms id
      | App (Own, [expr1; expr2; expr3], _) ->
        List.fold_left [expr1; expr3] ~f:(symbols bv) ~init:syms
      | App (_, ts, _) ->
	List.fold_left ts ~f:(symbols bv) ~init:syms
      | Binder (_, vs, e, _) ->
        let syms =
          List.fold_left vs
            ~init:syms ~f:(fun syms var_decl -> Type.symbols ~acc:syms var_decl.var_type)
        in
        let bv =
          List.fold_left vs
            ~init:bv ~f:(fun bv var_decl -> Set.add bv (QualIdent.from_ident var_decl.var_name))
        in
        symbols bv syms e
    in 
    symbols (Set.empty (module QualIdent)) acc e 


  (** Returns the set of local variables in expression [t]. *)
  let rec local_vars (expr: t) : IdentSet.t =
    let sign = signature expr in
    Map.fold sign ~f:(fun ~key ~data:_ locals ->
        if QualIdent.is_qualified key
        then locals
        else Set.add locals (QualIdent.unqualify key))
      ~init:(Set.empty (module Ident))


  (** Returns list of heaps accessed in expressions. Can return duplicates. Deduplication happens in stmt_heaps_accessed. *)
  (* TODO: rewrite to use Expr.signature instead *)
  let rec expr_fields_accessed (expr: t) : qual_ident list =
    match expr with
    (* Following can be strengthened to exactly 3 args, once we implement rewriting 4-arg Own predicates to 3-arg Own predicates during typing, using $Library.Frac *)
    | App (Own, expr1 :: expr2 :: expr3s, _expr_attr) ->
      (match expr2 with
      | App (Var qual_ident, [], _expr_attr) ->
        [qual_ident]
      | _ -> assert false)

    | App (Read, expr1 :: expr2 :: [], _expr_attr) ->
      (match expr2 with
      | App (Var qual_ident, [], _expr_attr) ->
        [qual_ident]
      | _ -> assert false)
      

    | App (_constr, expr_list, _expr_attr) ->
      List.concat_map expr_list ~f:(fun expr -> expr_fields_accessed expr)

    | Binder (_binder, var_decl_list, expr, _expr_attr) ->
      expr_fields_accessed expr
end

type expr = Expr.t


(** Statements *)

module Stmt = struct
  type spec = {
    spec_form : expr;
    spec_atomic : bool;
    spec_error : (qual_ident -> string * string) option;
  }

  type var_def = { var_decl : var_decl; var_init : expr option }

  type new_desc = {
    new_lhs : qual_ident;
    new_args : (qual_ident * expr option) list;
  }

  type assign_desc = { assign_lhs : expr list; assign_rhs : expr }
  type bind_desc = { bind_lhs : expr list; bind_rhs : expr }

  type call_desc = {
    call_lhs : qual_ident list;
    call_name : qual_ident;
    call_args : expr list;
  }

  type fold_desc = { fold_expr : expr }
  type unfold_desc = { unfold_expr : expr }

  type fpu_desc = {
    fpu_ref : expr;
    fpu_field : qual_ident;
    fpu_val : expr
  }

  type spec_kind =
    | Assume | Assert | Inhale | Exhale

  let assume_string = "assume"
  let assert_string = "assert"
  let inhale_string = "inhale"
  let exhale_string = "exhale"

  let spec_kind_to_string = function
    | Assume -> assume_string
    | Assert -> assert_string
    | Inhale -> inhale_string
    | Exhale -> exhale_string

  type use_kind =
    | Fold
    | Unfold
    | OpenInv
    | CloseInv

  let use_kind_to_string = function
    | Fold -> "fold"
    | Unfold -> "unfold"
    | OpenInv -> "openInv"
    | CloseInv -> "closeInv"

  type use_desc = {
    use_kind : use_kind;
    use_name : qual_ident;
    use_args : expr list;
  }

  type auaction_kind =
    | BindAU of qual_ident
    | OpenAU of qual_ident
    | AbortAU
    | CommitAU

  let auaction_kind_to_string = function
    | BindAU _ -> "bindAU"
    | OpenAU _ -> "openAU"
    | AbortAU -> "abortAU"
    | CommitAU -> "commitAU"

  type auaction_desc = {
    auaction_kind : auaction_kind;
  }
  
  type basic_stmt_desc =
    | VarDef of var_def
    | Spec of spec_kind * spec (* x *)
    | New of new_desc
    | Assign of assign_desc (* x *)
    | Bind of bind_desc (* x *)
    | Havoc of qual_ident (* x *)
    | Call of call_desc
    | Return of expr
    | Use of use_desc
    | AUAction of auaction_desc
    | Fpu of fpu_desc

  type t = { stmt_desc : stmt_desc; stmt_loc : location }

  and loop_desc = {
    loop_contract : spec list;  (** the loop invariant *)
    loop_prebody : t;
        (** the statement executed before testing the loop condition *)
    loop_test : expr;  (** the loop condition *)
    loop_postbody : t;  (** the actual loop body *)
  }

  and cond_desc = { cond_test : expr; cond_then : t; cond_else : t }
  and block_desc = { block_body : t list; block_is_ghost: bool }

  and stmt_desc =
    | Block of block_desc
    | Basic of basic_stmt_desc
    | Loop of loop_desc
    | Cond of cond_desc

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
        fprintf ppf "@<0>%s%s %a@\n%a"
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
    | Bind bstm -> (
      match bstm.bind_lhs with
      | [] -> Expr.pr ppf bstm.bind_rhs
      | es ->
          fprintf ppf "@[<2>%a@ :|@ %a@]" Expr.pr_list es Expr.pr
          bstm.bind_rhs)

    | Havoc x -> fprintf ppf "@[<2>havoc@ %a@]" QualIdent.pr x
    | New nstm -> 
        fprintf ppf "@[<2>%a@ :=@ new@ %a@]" QualIdent.pr nstm.new_lhs
          (Print.pr_list_comma (fun ppf -> function
            | (f, Some e) -> fprintf ppf "%a:@ %a" QualIdent.pr f Expr.pr e
            | (f, None) -> QualIdent.pr ppf f))
          nstm.new_args

    | Spec (spec_kind, sf) -> pr_spec_list (spec_kind_to_string spec_kind) ppf [ sf ]
    | Use use_desc ->
      fprintf ppf "@[<2>%s %a(@[%a@])@]"
        (use_kind_to_string use_desc.use_kind)
        QualIdent.pr use_desc.use_name
        Expr.pr_list use_desc.use_args
    | Return e -> fprintf ppf "@[<2>return@ %a@]" Expr.pr e
    | Call cstm -> (
        match cstm.call_lhs with
        | [] ->
            fprintf ppf "@[%a(@[%a@])@]" QualIdent.pr cstm.call_name
              Expr.pr_list cstm.call_args
        | _ ->
            fprintf ppf "@[<2>%a@ :=@ @[%a(@[%a@])@]@]" QualIdent.pr_list
              cstm.call_lhs QualIdent.pr cstm.call_name Expr.pr_list
              cstm.call_args)
    | AUAction { auaction_kind = BindAU token} ->
      fprintf ppf "@[<2>%a := %s()@]" QualIdent.pr token (auaction_kind_to_string (BindAU token))
    | AUAction { auaction_kind = OpenAU token} ->
      fprintf ppf "@[<2>%s(%a)@]" (auaction_kind_to_string (OpenAU token)) QualIdent.pr token
    | AUAction { auaction_kind; _} ->
      fprintf ppf "@[<2>%s()@]" (auaction_kind_to_string auaction_kind)
    | Fpu fpu_desc -> fprintf ppf "@[<2>fpu %a.%a ~> %a@]" Expr.pr fpu_desc.fpu_ref QualIdent.pr fpu_desc.fpu_field Expr.pr fpu_desc.fpu_val

  let rec pr ppf stmt =
    let open Stdlib.Format in
    match stmt.stmt_desc with
    | Loop ldesc ->
        fprintf ppf "%awhile (%a)@ @,@[<2>@ @ %a@]@\n%a"
          (fun ppf -> function
            | { stmt_desc = Block { block_body = []; _ }; _ } -> ()
            | s -> pr ppf s)
          ldesc.loop_prebody Expr.pr ldesc.loop_test (pr_spec_list "invariant")
          ldesc.loop_contract pr ldesc.loop_postbody
    | Cond cdesc -> (
        match cdesc.cond_else.stmt_desc with
        | Block { block_body = []; _ } ->
            fprintf ppf "if (@[%a@]) %a" Expr.pr cdesc.cond_test pr
              cdesc.cond_then
        | _ ->
            fprintf ppf "if (@[%a@]) %a@ else@ %a" Expr.pr cdesc.cond_test pr
              cdesc.cond_then pr cdesc.cond_else)
    | Block { block_body = stmts; block_is_ghost = false } -> 
        begin match stmts with
          | [] -> fprintf ppf "{ }"
          | _ -> fprintf ppf "{@\n  @[%a@]@\n}" pr_block stmts
        end
    | Block { block_body = stmts; block_is_ghost = true } ->
        begin match stmts with
          | [] -> fprintf ppf "{! !}"
          | _ -> fprintf ppf "{!@\n  @[%a@]@\n!}" pr_block stmts
        end
    | Basic bs -> pr_basic_stmt ppf bs

  and pr_block ppf stmts = Print.pr_list_nl pr ppf stmts

  let to_string s = Print.string_of_format pr s
  let print chan s = Print.print_of_format pr s chan

  (** Constructors *)

  let mk_skip ~loc = { stmt_desc = Block { block_body = []; block_is_ghost = false }; stmt_loc = loc }

  let mk_block ?(ghost=false) stmts = 
    let stmts = List.concat_map stmts ~f:(function
      | { stmt_desc = Block { block_body; block_is_ghost }; _ } -> block_body
      | s -> [s]) in

    Block { block_body = stmts; block_is_ghost = ghost }

  let mk_block_stmt ~loc ?(ghost=false) stmts = 
    { stmt_desc = mk_block ~ghost stmts; stmt_loc = loc }

  let mk_assume_expr ~loc expr : t = 
    let spec = { spec_form = expr; spec_atomic = false; spec_error = None } in
    { stmt_desc = Basic (Spec (Assume, spec)); stmt_loc = loc }

  let mk_assume_spec ~loc spec : t = 
    { stmt_desc = Basic (Spec (Assume, spec)); stmt_loc = loc }

  let mk_inhale_expr ~loc expr : t = 
    let spec = { spec_form = expr; spec_atomic = false; spec_error = None } in
    { stmt_desc = Basic (Spec (Inhale, spec)); stmt_loc = loc }

  let mk_inhale_spec ~loc spec : t = 
    { stmt_desc = Basic (Spec (Inhale, spec)); stmt_loc = loc }

  let mk_exhale_expr ~loc expr : t = 
    let spec = { spec_form = expr; spec_atomic = false; spec_error = None } in
    { stmt_desc = Basic (Spec (Exhale, spec)); stmt_loc = loc }

  let mk_exhale_spec ~loc spec : t = 
    { stmt_desc = Basic (Spec (Exhale, spec)); stmt_loc = loc }
  
  let mk_assert_expr ~loc expr : t = 
    let spec = { spec_form = expr; spec_atomic = false; spec_error = None } in
    { stmt_desc = Basic (Spec (Assert, spec)); stmt_loc = loc }

  let mk_assert_spec ~loc spec : t =
    { stmt_desc = Basic (Spec (Assert, spec)); stmt_loc = loc }


  let mk_havoc ~loc x = { stmt_desc = Basic (Havoc x); stmt_loc = loc }

  let mk_cond ~loc test then_ else_ =
    { stmt_desc = Cond { cond_test = test; cond_then = then_; cond_else = else_ }; stmt_loc = loc }

  let mk_call ~loc ?(lhs=[]) name args =
    { stmt_desc = Basic (Call { call_lhs = lhs; call_name = name; call_args = args }); stmt_loc = loc }

  let mk_assign ~loc lhs rhs =
    { stmt_desc = Basic (Assign { assign_lhs = lhs; assign_rhs = rhs }); stmt_loc = loc }

  let mk_return ~loc e = { stmt_desc = Basic (Return e); stmt_loc = loc }

  (** Auxiliary functions *)

  let mk_spec ?(atomic = false) ?(error = None) e = 
    {
      spec_form = e;
      spec_atomic = atomic;
      spec_error = error;
    }

  let loc s = s.stmt_loc

  (** Extends [accessed] with the set of all symbols occuring free in [s] *)
  (** Assumes that all var_decl stmts are abstracted away during type-checking. *)  
  let symbols ?(accessed = Set.empty (module QualIdent)) (s: t) : QualIdentSet.t =
    let rec symbols (accesses: QualIdentSet.t) (s: t) =
      let scan_expr_list accesses exprs =
        List.fold exprs
          ~f:(fun accesses e -> Expr.symbols ~acc:accesses e)
          ~init:accesses
      in
      match s.stmt_desc with
      | Block b ->
        List.fold b.block_body ~f:symbols ~init:accesses

      | Basic s1 -> 
        begin match s1 with
        | VarDef _ ->
          Error.internal_error s.stmt_loc "VarDef should not exist in Stmt.symbols"

        | Spec (_, spec) ->
          Expr.symbols ~acc:accesses spec.spec_form 

        | New new_desc ->
          let accesses =
            List.fold new_desc.new_args ~f:(fun accesses (_, e_opt) ->
                Option.map e_opt ~f:(Expr.symbols ~acc:accesses) |>
                Option.value ~default:accesses) ~init:accesses
          in
          Set.add accesses new_desc.new_lhs

        | Assign assign_desc ->
          scan_expr_list accesses (assign_desc.assign_rhs :: assign_desc.assign_lhs)
        
        | Bind bind_desc ->
          scan_expr_list accesses (bind_desc.bind_rhs :: bind_desc.bind_lhs)
            
        | Havoc x ->
          Set.add accesses x

        | Call call_desc ->
          let accesses = scan_expr_list accesses call_desc.call_args in
          let accesses =
            List.fold call_desc.call_lhs
              ~f:Set.add
              ~init:accesses
          in
          accesses

        | Return e ->
          Expr.symbols ~acc:accesses e
          
        | Use use_desc ->
          scan_expr_list accesses use_desc.use_args

        | AUAction _ -> accesses

        | Fpu fpu_desc ->
          scan_expr_list accesses [fpu_desc.fpu_ref; fpu_desc.fpu_val]
        end

      | Loop l ->
        let accesses = Expr.symbols ~acc:accesses l.loop_test in
        let accesses_prebody = symbols accesses l.loop_prebody in
        symbols accesses_prebody l.loop_postbody

      | Cond c ->
        let accesses = Expr.symbols ~acc:accesses c.cond_test in
        let accesses_then = symbols accesses c.cond_then in
        symbols accesses_then c.cond_else
    in
    symbols accessed s

  let local_vars_accessed (s: t) : IdentSet.t =
    let sign = symbols s in
    Set.fold sign ~f:(fun locals id ->
        if QualIdent.is_qualified id
        then locals
        else Set.add locals (QualIdent.unqualify id))
      ~init:(Set.empty (module Ident))


  let stmt_local_vars_modified (s: t) : ident list =
    let rec stmt_locals_modified (s: t): (ident list) =
      (* Returns all local variables modified in s.
        Assumes that all var_decl stmts are abstracted away during type-checking.   
      *)

      match s.stmt_desc with
      | Block b ->
        List.concat_map b.block_body ~f:(fun s -> stmt_locals_modified s)

      | Basic s1 -> 
        begin match s1 with
        | VarDef _ ->
          Error.internal_error s.stmt_loc "VarDef should not exist in stmt_local_vars_modified"

        | Spec _ ->
          []

        | New new_desc ->
          if List.is_empty new_desc.new_lhs.qual_path then
              [new_desc.new_lhs.qual_base]
          else
            []

        | Assign assign_desc ->
          List.filter_map assign_desc.assign_lhs ~f:(fun e -> 
            match e with
            | App (Var qi, _, _) -> 
              if List.is_empty qi.qual_path then
                Some qi.qual_base
              else
                None
            | _ -> None
          )

        | Bind bind_desc ->
          List.filter_map bind_desc.bind_lhs ~f:(fun e -> 
            match e with
            | App (Var qi, _, _) -> 
              if List.is_empty qi.qual_path then
                Some qi.qual_base
              else
                None
            | _ -> None
          )
          
        | Havoc x ->
          if List.is_empty x.qual_path then 
            [x.qual_base]
          else 
            (Error.internal_error s.stmt_loc "Only local variables should be havoc-ed; caugh in stmt_local_vars_modified")

        | Call call_desc ->
          List.filter_map call_desc.call_lhs ~f:(fun qi -> 
            if List.is_empty qi.qual_path then
              Some qi.qual_base
            else
              None
          )

        | Return _ ->
          []
          
        | Use _ ->
          []

        | AUAction _ -> []

        | Fpu fpu_desc ->
          (match fpu_desc.fpu_ref with
            | App (Var qi, _, _) -> 
              if List.is_empty qi.qual_path then
                [qi.qual_base]
              else
                []
            | _ -> [])
        end

      | Loop l ->
        let modified_prebody = stmt_locals_modified l.loop_prebody in
        let modified_postbody = stmt_locals_modified l.loop_postbody in
        modified_prebody @ modified_postbody

      | Cond c ->
        let modified_then = stmt_locals_modified c.cond_then in
        let modified_else = stmt_locals_modified c.cond_else in
        modified_then @ modified_else

    in

    let modifieds = stmt_locals_modified s in
    let modifieds = List.dedup_and_sort modifieds ~compare:Ident.compare in
    modifieds


  let stmt_fields_accessed (s: t) : qual_ident list =
    let rec stmt_fields_accessed (s: t): (qual_ident list) =
      (* Returns all field heaps accessed in s. *)

      match s.stmt_desc with
      | Block b ->
        List.concat_map b.block_body ~f:(fun s -> stmt_fields_accessed s)

      | Basic s1 -> 
        begin match s1 with
        | VarDef _ ->
          Error.internal_error s.stmt_loc "VarDef should not exist in the AST during stmt_fields_accessed"

        | Spec (_, s) ->
          Expr.expr_fields_accessed s.spec_form

        | New _ ->
          []

        | Assign assign_desc ->
          List.concat_map (assign_desc.assign_rhs :: assign_desc.assign_lhs) ~f:(fun e -> Expr.expr_fields_accessed e)
        
        | Bind bind_desc ->
          List.concat_map (bind_desc.bind_rhs :: bind_desc.bind_lhs) ~f:(fun e -> Expr.expr_fields_accessed e)

        | Havoc _ ->
          []

        | Call call_desc ->
          Error.internal_error s.stmt_loc "Call stmts should not exist in the AST during stmt_fields_accessed"

        | Return _ ->
          []
          
        | Use _ ->
          []

        | AUAction _ -> []

        | Fpu fpu_desc ->
          [fpu_desc.fpu_field]
        end

      | Loop l ->
        let heaps_accessed_prebody = stmt_fields_accessed l.loop_prebody in
        let heaps_accessed_postbody = stmt_fields_accessed l.loop_postbody in
        heaps_accessed_prebody @ heaps_accessed_postbody

      | Cond c ->
        let heaps_accessed_then = stmt_fields_accessed c.cond_then in
        let heaps_accessed_else = stmt_fields_accessed c.cond_else in
        heaps_accessed_then @ heaps_accessed_else

    in

    let heaps_accessed = stmt_fields_accessed s in
    let heaps_accessed = List.dedup_and_sort heaps_accessed ~compare:QualIdent.compare in
    heaps_accessed
end


(** Callables *)

module Callable = struct
  type call_kind = 
    | Proc | Lemma (* proc *)
    | Func | Pred | Invariant (* func *)

  type call_decl = {
    call_decl_kind : call_kind;  (** kind of declaration *)
    call_decl_name : ident;  (** name of associated declaration *)
    call_decl_formals : var_decl list;  (** formal parameter list *)
    call_decl_returns : var_decl list;  (** return parameter list *)
    call_decl_locals : var_decl list;  (** all local variables, excluding formal parameters and return parameters *)
    call_decl_precond : Stmt.spec list;  (** precondition *)
    call_decl_postcond : Stmt.spec list;  (** postcondition *)
    call_decl_is_free : bool; (** Indicates whether the correctness of this callable comes for free or needs to be checked *)
    call_decl_is_auto : bool;
    call_decl_loc : location;  (** source location of declaration *)
  }

  type call_def =
    | ProcDef of { proc_body : Stmt.t option }
    | FuncDef of { func_body : expr option }

  type t = { call_decl : call_decl; call_def : call_def }

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
          fprintf ppf "@\nreturns (@[<0>%a@])" Expr.pr_var_decl_list rs
    in
    let pr_call_locals ppf = function
      | [] -> ()
      | ls ->
          fprintf ppf "@\nlocals (@[<0>%a@])" Expr.pr_var_decl_list ls
    in
    fprintf ppf "@[<2>%s %a(@[<0>%a@])%a%a%a@]" 
      kind 
      Ident.pr call_decl.call_decl_name 
      (Print.pr_list_comma Expr.pr_var_decl) call_decl.call_decl_formals
      pr_returns call_decl.call_decl_returns 
      pr_call_decl_specs call_decl
      pr_call_locals call_decl.call_decl_locals

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
    | { call_decl; call_def = FuncDef fdef} ->
        fprintf ppf "%a%a" pr_call_decl call_decl (pr_fn_body Expr.pr)
          fdef.func_body
    | { call_decl; call_def = ProcDef pdef} ->
        fprintf ppf "%a%a" pr_call_decl call_decl (pr_proc_body Stmt.pr)
          pdef.proc_body

  (** Auxiliary functions *)

  let to_decl (call: t) = call.call_decl

  let to_ident (call: t) = call |> to_decl |> fun call_decl -> call_decl.call_decl_name

  let to_loc (call: t) = call |> to_decl |> fun call_decl -> call_decl.call_decl_loc

  let kind (call: t) = call |> to_decl |> fun call_decl -> call_decl.call_decl_kind
  
  let return_decls call_decl = 
    call_decl.call_decl_returns
  
  let return_type call_decl =
    match call_decl.call_decl_kind with
    | Proc | Func | Lemma ->
      let returns = 
        List.map call_decl.call_decl_returns
          ~f:(fun r -> r.var_type)
      in
      begin match returns with
      | [] -> Type.unit
      | [t] -> t
      | ts -> Type.mk_prod call_decl.call_decl_loc ts
      end
    | Pred | Invariant -> Type.perm

  (** Computes the set of all symbols occuring free in [callable]. *)
  let symbols callable =
    let symbols_w_locals =
      match callable.call_def with
      | FuncDef { func_body = Some e; _} ->
        Expr.symbols e
      | ProcDef { proc_body = Some s; _ } -> Stmt.symbols s
      | _ -> Set.empty (module QualIdent)
    in
    let symbols_w_locals_and_spec =
      List.fold ~f:(fun syms spec -> Expr.symbols ~acc:syms spec.spec_form)
        ~init:symbols_w_locals
        (callable.call_decl.call_decl_precond @ callable.call_decl.call_decl_postcond)
    in
    List.fold ~f:(fun syms var_decl ->
          let qi = QualIdent.from_ident var_decl.var_name in
          (* Remove qi if it occurs but add all symbols from its type *)
          if Set.mem syms qi
          then Type.symbols ~acc:(Set.remove syms qi) var_decl.var_type
          else syms)
      ~init:symbols_w_locals_and_spec
      (callable.call_decl.call_decl_formals @ callable.call_decl.call_decl_returns @ callable.call_decl.call_decl_locals)

  (** Change the given symbol to one whose correctness is assumed *)
  let make_free call_def = 
    { call_def with call_decl = { (to_decl call_def) with call_decl_is_free = true } }
end


(** Modules *)

module Module = struct
  type type_def = {
    type_def_name : ident;
    type_def_expr : type_expr option;
    type_def_rep : bool;
    type_def_loc : location;
  }

  type constr_def = {
    constr_name : Ident.t;
    constr_loc : location;
    constr_args : var_decl list;
    constr_return_type : type_expr;
  }

  type destr_def = {
    destr_name : Ident.t;
    destr_loc : location;
    destr_arg : type_expr;
    destr_return_type : type_expr;
  }

  type module_inst = {
    mod_inst_name : ident;
    mod_inst_type : QualIdent.t;
    mod_inst_def : (QualIdent.t * QualIdent.t list) option;
    mod_inst_is_interface : bool;
    mod_inst_loc : location;
  }

  type field_def = {
    field_name : ident; 
    field_type : type_expr; 
    field_loc : Loc.t 
  }

  type module_decl = {
    mod_decl_name : ident;
    mod_decl_formals : module_inst list;
    mod_decl_returns : QualIdent.t option;
    mod_decl_interfaces : QualIdentSet.t;
    mod_decl_rep : ident option;
    mod_decl_is_ra : bool;
    mod_decl_is_interface : bool;
    mod_decl_loc : location;
  }

  type import_directive = {
    import_name : qual_ident;
    import_loc : location
  }

  type symbol =
    | ModDef of t
    | ModInst of module_inst
    | TypeDef of type_def
    | ConstrDef of constr_def
    | DestrDef of destr_def
    | FieldDef of field_def
    | VarDef of Stmt.var_def
    | CallDef of Callable.t

  and module_instr =
    | SymbolDef of symbol
    | Import of import_directive

  and t = {
    mod_decl : module_decl;
    mod_def : module_instr list;
  }

  let rec pr ppf md =
    let open Stdlib.Format in
    let mod_vs =
      List.map md.mod_decl.mod_decl_formals ~f:(fun v ->
          (v.mod_inst_name, v.mod_inst_type))
    in
    fprintf ppf "@[<2>%s@ %a%a%a@]@\n{@[<1>@\n%a@]@\n}"
      (if md.mod_decl.mod_decl_is_interface then "interface" else "module")
      Ident.pr md.mod_decl.mod_decl_name
      (* formal parameters *)
        (fun ppf -> function
          | [] -> ()
          | vs -> fprintf ppf "[@[%a@]]" (Print.pr_list_comma (fun ppf (v, t) -> fprintf ppf "%a: %a" Ident.pr v QualIdent.pr t)) vs)
        mod_vs
      (* return types *)
        (fun ppf -> function
          | [] -> ()
          | vs -> fprintf ppf "@ : %a" QualIdent.pr_list vs)
      (Option.to_list md.mod_decl.mod_decl_returns) (* body *) pr_instr_list md.mod_def

  and pr_instr ppf =
    let open Stdlib.Format in
    function
    | SymbolDef symbol -> pr_symbol ppf symbol
    | Import { import_name = qid; _ } -> fprintf ppf "@[<2>import@ %a@]" QualIdent.pr qid

  and pr_instr_list ppf ms = Print.pr_list_sep "@\n@\n" pr_instr ppf ms

  and pr_symbol ppf =
    let open Stdlib.Format in
    function
    | ModDef md -> pr ppf md
    | ModInst ma ->
        fprintf ppf "@[<2>module@ %a : %a%a@]" Ident.pr ma.mod_inst_name
          QualIdent.pr ma.mod_inst_type
          (fun ppf -> function
            | None -> ()
            | Some (t, ts) -> fprintf ppf " =@ %a[%a]" QualIdent.pr t QualIdent.pr_list ts)
          ma.mod_inst_def
    | TypeDef ta ->
        fprintf ppf "%stype %a%a"
          (if ta.type_def_rep then "rep " else "")
          Ident.pr ta.type_def_name
          (fun ppf -> function
            | None -> ()
            | Some t -> fprintf ppf " = %a" Type.pr t)
          ta.type_def_expr
    | ConstrDef cdef ->
      fprintf ppf "/* constr %a(%a): %a */"
        Ident.pr cdef.constr_name
        Type.pr_list (List.map cdef.constr_args ~f:(fun var_decl -> var_decl.var_type))
        Type.pr cdef.constr_return_type
    | DestrDef def ->
      fprintf ppf "/* destr %a(%a): %a */"
        Ident.pr def.destr_name
        Type.pr def.destr_arg
        Type.pr def.destr_return_type
    | FieldDef field_def ->
      let field_type = match field_def.field_type with
        | App (Fld, [typ], _) -> typ
        | typ -> typ
      in
      fprintf ppf "field %a: %a" Ident.pr field_def.field_name Type.pr
        field_type
    | VarDef vdef -> Stmt.pr_var_def ppf vdef
    | CallDef cdef -> Callable.pr ppf cdef
                     
  let to_string m = Print.string_of_format pr m
  let print chan m = Print.print_of_format pr m chan
  (*let print_verbose chan m = Print.print_of_format pr_verbose m chan*)
  let print_member_list chan ms = Print.print_of_format pr_instr_list ms chan

  (** Constructors *)

  let empty_decl =
    {
      mod_decl_name = Ident.make Loc.dummy "" 0;
      mod_decl_formals = [];
      mod_decl_returns = None;
      mod_decl_interfaces = Set.empty (module QualIdent);
      mod_decl_rep = None;
      mod_decl_loc = Loc.dummy;
      mod_decl_is_ra = false;
      mod_decl_is_interface = false;
    }


  (** Auxiliary functions *)

  let to_ident m = m.mod_decl.mod_decl_name
      
  let rec find_mod (mod_defs: t list) (name: Ident.t) =
    match mod_defs with
    | [] -> Error.error Loc.dummy @@ Printf.sprintf "Module %s not found in list " (Ident.to_string name)
    | mod_def :: mod_defs ->
      if Ident.equal mod_def.mod_decl.mod_decl_name name then
        mod_def
      else
        find_mod mod_defs name

  let find_callable (call_defs: Callable.t list) (name: ident) =
    let res = List.find call_defs ~f:(fun call_def -> Ident.equal (Callable.to_decl call_def).call_decl_name name) in
    match res with
    | None -> Error.error Loc.dummy @@ Printf.sprintf "Callable %s not found in list " (Ident.to_string name)
    | Some call_def -> call_def

  let rec find_var (var_defs: Stmt.var_def list) (name: Ident.t) = 
    match var_defs with
    | [] -> Error.error Loc.dummy @@ Printf.sprintf "Variable %s not found in list " (Ident.to_string name)
    | var_def :: var_defs ->
      if Ident.equal (var_def.var_decl.var_name) name then
        var_def
      else
        find_var var_defs name

  let set_name md name =
    { md with mod_decl = { md.mod_decl with mod_decl_name = name } }



end

(** Symbols (for convenience) *)

module Symbol = struct
  type t = Module.symbol
  open Module
      
  let to_loc = function
    | ModDef mod_def -> mod_def.mod_decl.mod_decl_loc
    | ModInst mod_inst -> mod_inst.mod_inst_loc
    | TypeDef type_def -> type_def.type_def_loc
    | ConstrDef cdef -> cdef.constr_loc
    | DestrDef cdef -> cdef.destr_loc
    | FieldDef field_def -> field_def.field_loc
    | VarDef var_def -> var_def.var_decl.var_loc
    | CallDef call_def -> Callable.to_loc call_def

  let to_name = function
    | ModDef mod_def -> mod_def.mod_decl.mod_decl_name
    | ModInst mod_inst -> mod_inst.mod_inst_name
    | TypeDef type_def -> type_def.type_def_name
    | ConstrDef cdef -> cdef.constr_name
    | DestrDef cdef -> cdef.destr_name
    | VarDef var_def -> var_def.var_decl.var_name
    | FieldDef field_def -> field_def.field_name
    | CallDef call_def -> Callable.to_ident call_def

  let kind = function
    | TypeDef _ -> "type"
    | ModInst mod_inst when mod_inst.mod_inst_is_interface -> "interface"
    | ModDef mod_def when mod_def.mod_decl.mod_decl_is_interface -> "interface"
    | ModDef _ | ModInst _ -> "module"
    | VarDef var_def when var_def.var_decl.var_const -> "value"
    | VarDef _ -> "variable"
    | ConstrDef _ -> "constructor"
    | DestrDef _ -> "destructor"
    | FieldDef _ -> "field"
    | CallDef call_def ->
      match call_def.call_decl.call_decl_kind with
      | Lemma -> "lemma"
      | Proc -> "procedure"
      | Func -> "function"
      | Pred -> "predicate"
      | Invariant -> "invariant"

  let pr = pr_symbol

  let to_string m = Print.string_of_format pr m

end


module Predefs = struct
  let lib_ident = (Ident.make Loc.dummy "Library" 0)

  let prog_ident = Ident.make Loc.dummy "$Program" 0
  let prog_qual_ident = QualIdent.from_ident prog_ident

  let lib_type_mod_ident = Ident.make Loc.dummy "Type" 0
  let lib_type_mod_qual_ident = QualIdent.from_list [lib_ident; lib_type_mod_ident]
  let lib_type_rep_type_ident = Ident.make Loc.dummy "T" 0

  let lib_ra_mod_qual_ident = QualIdent.from_list [lib_ident; Ident.make Loc.dummy "ResourceAlgebra" 0]

  let lib_cancellative_ra_mod_qual_ident = QualIdent.from_list [lib_ident; Ident.make Loc.dummy "CancellativeResourceAlgebra" 0]

  let lib_frac_mod_qual_ident = QualIdent.from_list [lib_ident; Ident.make Loc.dummy "Frac" 0]



end
