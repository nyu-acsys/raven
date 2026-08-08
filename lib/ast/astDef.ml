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

    let set_loc loc id = { id with ident_loc = loc }
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

  let sanitized_name name =
    String.map name ~f:(fun c ->
      match c with
      | '^' -> '&'
      | c -> c
    )

  let make loc name num = 
    let name = sanitized_name name in 

    { ident_name = name; ident_num = num; ident_loc = loc }
  let name id = id.ident_name

  let used_names = Hashtbl.create (module String)

  let fresh loc =
    fun ?(id = 0) (name : string) ->
      let name = sanitized_name name in
      let last_index =
        Hashtbl.find used_names name |> Option.value ~default:(-1)
      in
      let new_max = Int.max (last_index + 1) id in
      (* Logs.debug (fun m -> m "Keyset: %d" (List.count (Hashtbl.keys used_names) ~f:(fun _ -> true)));
      Logs.debug (fun m -> m "old id %s -> %d" name last_index);
      Logs.debug (fun m -> m "fresh id %s -> %d" name new_max); *)
      Hashtbl.set used_names ~key:name ~data:new_max;
      make loc name new_max

  let sanitize subst id = { id with
    ident_name = String.map ~f:subst id.ident_name
  }
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

  let set_loc loc qid =
    { qid with qual_base = Ident.set_loc loc qid.qual_base }
  
  let first_ident qid =
    match qid.qual_path with
    | id :: _ -> id
    | [] -> qid.qual_base
      
  let pr ppf qid =
    let path = match qid.qual_path with
      | maybe_program :: path when String.(Ident.name maybe_program = "$Program") -> path
      | path -> path
    in
    Print.pr_list_sep "." Ident.pr ppf (path @ [qid.qual_base])

  (* let pr ppf qid = Print.pr_list_sep "." Ident.pr ppf (qid.qual_path @ [qid.qual_base]) *)

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

  let sanitize subst qid = 
    from_list
      (List.map ~f:(fun iden -> Ident.sanitize subst iden) (to_list qid))
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
    type type_ext = ..

    let default_type_ext_to_name : type_ext -> string = fun _ -> "[TypeExt]"

    let compare_type_ext (c1: type_ext) (c2: type_ext) =
      Stdlib.compare (Stdlib.Obj.tag (Stdlib.Obj.repr c1)) (Stdlib.Obj.tag (Stdlib.Obj.repr c2))

    let equal_type_ext (c1 : type_ext) (c2 : type_ext) : bool =
      compare_type_ext c1 c2 = 0

    let hash_fold_type_ext state te =
      let tag = Stdlib.Obj.tag (Stdlib.Obj.repr te) in
        Ppx_hash_lib.Std.Hash.fold_int state tag
    
    let type_ext_of_sexp : (Sexp.t -> type_ext) = (fun sexp -> Sexplib.Conv.of_sexp_error "type_ext_of_sexp: unexpected sexp" sexp)

    let sexp_of_type_ext : (type_ext -> Sexp.t) = (fun type_ext -> Sexplib.Conv.sexp_of_opaque type_ext)

    type type_attr = {
      type_loc : Loc.t; [@hash.ignore] [@compare.ignore]
      type_ghost: bool [@hash.ignore] [@compare.ignore]
    }

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
      | Map
      | FinSet
      | Fld
      | Data of QualIdent.t * variant_decl list
      | AtomicToken of QualIdent.t
      | Prod
      | TypeExt of type_ext

    and t = App of constr * t list * type_attr
    [@@deriving compare, hash, sexp]
  end

  include T
  include Comparable.Make (T)
    
  let attr_of = function App (_, _, attr) -> attr
  let to_loc t = t |> attr_of |> fun attr -> attr.type_loc

  let is_ghost t = t |> attr_of |> fun attr -> attr.type_ghost
  let set_ghost b =
    let rec f = 
      function App (constr, args, attr) ->
        let args = List.map args ~f in
        App (constr, args, { attr with type_ghost = b })
    in f
  let set_ghost_to t1 t2 = set_ghost (is_ghost t1) t2
  
  (** Pretty printing types *)

  let ref_type_string = "Ref"
  let map_type_string = "Map"
  let set_type_string = "Set"
  let finset_type_string = "FinSet"
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
  let prod_type_string = "Unit"

  let make_to_name ~type_ext_to_name = function
    | Int -> int_type_string
    | Real -> real_type_string
    | Num -> num_type_string
    | Bool -> bool_type_string
    | Bot -> bot_type_string
    | Any -> any_type_string
    | Ref -> ref_type_string
    | Map -> map_type_string
    | FinSet -> finset_type_string
    | Fld -> fld_type_string
    | Perm -> perm_type_string
    | Data (id, _) -> QualIdent.to_string id
    | Var id -> QualIdent.to_string id
    | AtomicToken id -> Printf.sprintf !"%s<%{QualIdent}>" atomic_token_type_string id
    | Prod -> prod_type_string
    | TypeExt type_ext -> type_ext_to_name type_ext

  let to_name t = make_to_name ~type_ext_to_name:default_type_ext_to_name t

  (** Builds the mutually-recursive printer family, parameterized by how to render
      [TypeExt] leaves. [make_printers ~type_ext_to_name:default_type_ext_to_name] below
      is what every caller gets by default; an extension-aware set is built the same way
      from the extension's own [type_ext_to_name]. *)
  let make_printers ~type_ext_to_name =
    let to_name = make_to_name ~type_ext_to_name in
    let rec pr_constr ppf t =
      match t with
      | Int | Real | Num | Bool | Any | Bot | Ref | Perm | Var _ | AtomicToken _
      | Map | FinSet | Fld | Prod | TypeExt _ ->
          Stdlib.Format.fprintf ppf "%s" (to_name t)
      | Data (id, decls) ->
        Stdlib.Format.fprintf ppf "data %a {@\n  @[%a@]@\n}"
          QualIdent.pr id
          pr_variant_decl_list decls

    and pr ppf t =
      match t with
      | App (t1, [], attr) -> Stdlib.Format.fprintf ppf "%a" pr_constr t1
      | App (Map, [t1; App (Bool, _, _)], _) ->
        Stdlib.Format.fprintf ppf "Set[%a]" pr t1
      | App (Prod, ts, _) ->
        Stdlib.Format.fprintf ppf "(@[%a@])" (Print.pr_list_comma pr) ts
      | App (t1, ts, _) ->
          Stdlib.Format.fprintf ppf "%a[%a]" pr_constr t1
            (Print.pr_list_comma pr) ts

    and pr_var_decl ppf decl =
      let open Stdlib.Format in
      fprintf ppf "%s%s @[<2>%a:@ %a@]"
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
      Stdlib.Format.fprintf ppf "%a: %a" Ident.pr id pr t

    and pr_arg_list ppf =
      Print.pr_list_comma
        (fun ppf decl -> pr_ident ppf (decl.var_name, decl.var_type))
        ppf
    in
    let pr_list ppf ts = Print.pr_list_comma pr ppf ts in
    let to_string t = Print.string_of_format pr t in
    ( pr_constr, pr, pr_var_decl, pr_var_decl_list, pr_variant_decl,
      pr_variant_decl_list, pr_ident, pr_arg_list, pr_list, to_string )

  let (pr_constr, pr, pr_var_decl, pr_var_decl_list, pr_variant_decl,
       pr_variant_decl_list, pr_ident, pr_arg_list, pr_list, to_string) =
    make_printers ~type_ext_to_name:default_type_ext_to_name

  (** Constructors *)

  let dummy_attr = { type_loc = Loc.dummy; type_ghost = false }
  let mk_attr ?(ghost=false) loc = if Loc.(loc = dummy) then dummy_attr else { type_loc = loc; type_ghost = ghost }
  let mk_app ?(loc = Loc.dummy) ?(ghost=false) t ts = App (t, ts, mk_attr ~ghost loc)

  let mk_int loc = App (Int, [], mk_attr loc)
  let mk_real loc = App (Real, [], mk_attr loc)
  let mk_num loc = App (Num, [], mk_attr loc)
  let mk_bool loc = App (Bool, [], mk_attr loc)
  let mk_unit loc = App (Prod, [], mk_attr loc)
  let mk_any loc = App (Any, [], mk_attr loc)
  let mk_bot loc = App (Bot, [], mk_attr loc)
  let mk_ref loc = App (Ref, [], mk_attr loc)
  let mk_set loc tp = App (Map, [tp; mk_bool loc], mk_attr loc)
  let mk_finset loc tp = App (FinSet, [tp], mk_attr loc)
  let mk_map loc tpi tpo = App (Map, [tpi; tpo], mk_attr loc)
  let mk_fld loc tpf = App (Fld, [tpf], mk_attr loc)
  let mk_perm loc = App (Perm, [], mk_attr loc)
  let mk_data id decls loc = App (Data (id, decls), [], mk_attr loc)
  let mk_var ?loc qid = 
    let loc = Option.value loc ~default:(QualIdent.to_loc qid) in

    App (Var qid, [], mk_attr loc)
  let mk_atomic_token loc qid = App (AtomicToken qid, [], mk_attr loc) |> set_ghost true
  let mk_prod loc tp_list = 
    match tp_list with
    | [tp] -> tp
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
  let finset_typed tp = mk_finset Loc.dummy tp
  let map = mk_map Loc.dummy
  let perm = mk_perm Loc.dummy |> set_ghost true
  let data id decls = mk_data id decls Loc.dummy
  let var qid = mk_var qid
  let atomic_token = mk_atomic_token Loc.dummy
  
  (** Equality and Subtyping *)

  (*let equal tp1 tp2 = ((compare tp1 tp2) = 0)*)
      
  let rec join_constr (t1: constr) t2 =
    if Poly.(t1 = t2) then t1 else
    match t1, t2 with
    | Bot, t | t, Bot -> t
    | Bool, Perm | Perm, Bool -> Perm
    | (Int | Real), (Int | Real) -> Real
    | (Int | Real | Num), (Int | Real | Num) when not @@ Poly.(t1 = t2) -> Num
    | TypeExt t1, TypeExt t2 ->
      if Int.(compare_type_ext t1 t2 = 0) then
        TypeExt t1
      else Any
    | _, _ -> Any
 
  let rec meet_constr t1 t2 = 
    if Poly.(t1 = t2) then t1 else
    match t1, t2 with
    | Any, t | t, Any -> t
    | Bool, Perm | Perm, Bool -> Bool
    | Int, Real | Real, Int -> Int
    | Int, Num | Num, Int -> Int
    | Real, Num | Num, Real -> Real
    | TypeExt t1, TypeExt t2 ->
      if Int.(compare_type_ext t1 t2 = 0) then 
        TypeExt t1
      else Bot
    | _, _ -> Bot

  let rec join t1 t2 =
    if equal t1 t2 then t1 else 
    match (t1, t2) with
    | App (Bot, [], _), t | t, App (Bot, [], _) -> t
    | App (t1, [], a1), App (t2, [], _) -> App (join_constr t1 t2, [], a1)
    | App (Map, [ti1; to1], a1), App (Map, [ti2; to2], _) -> App (Map, [meet ti1 ti2; join to1 to2], a1)
    | App (FinSet, [t1], a1), App (FinSet, [t2], _) -> App (FinSet, [meet t1 t2], a1)
    | App (FinSet, [t1], a1), App (Map, [t2; (App (Bool, _, _) as b)], _)
    | App (Map, [t2; (App (Bool, _, _) as b)], a1), App (FinSet, [t1], _) ->
      App (Map, [meet t1 t2; b], a1)
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
    | App (Map, [ti1; to1], a1), App (Map, [ti2; to2], _) -> App (Map, [join ti1 ti2; meet to1 to2], a1)
    | App (FinSet, [t1], a1), App (FinSet, [t2], _) -> App (FinSet, [join t1 t2], a1)
    | App (FinSet, [t1], a1), App (Map, [t2; App (Bool, _, _)], _)
    | App (Map, [t2; App (Bool, _, _)], a1), App (FinSet, [t1], _) ->
      App (FinSet, [join t1 t2], a1)
    | App (Prod, ts1, a1), App (Prod, ts2, _a2) ->
      (List.map2 ~f:meet ts1 ts2 |> function
      | Ok ts -> App (Prod, ts, a1)
      | _ -> App (Bot, [], a1))
    | App (Fld, [tf1], _), App (Fld, [tf2], _) when equal tf1 tf2 -> t1
    | App (_, _, a1), App (_, _, _) -> App (Bot, [], a1)

  let subtype_of tp1 tp2 = equal (join tp1 tp2) tp2
          
  (** Auxiliary utility functions *)
  
  let mk_var_decl ?(const = false) ?(ghost = false) ?(implicit = false) name ?(loc = Ident.to_loc name) tp =
    { var_name = name; var_loc = loc; var_type = tp |> set_ghost ghost; var_const = const; var_ghost = ghost; var_implicit = implicit }

  let is_num tp =
    equal tp real || equal tp int

  let is_any tp_expr = equal tp_expr any

  (** True iff [Bot] occurs anywhere in [tp_expr], e.g. `Set(Bot)` -- the type an
      empty collection literal (`{||}`) is given absent any expected type to pin
      down its element type. Such a type carries no real information and should
      never be treated as a successfully inferred type argument. *)
  let rec contains_bot = function
    | App (Bot, _, _) -> true
    | App (_, ts, _) -> List.exists ts ~f:contains_bot

  let is_set tp_expr = match tp_expr with
    | App (Map, [_; App(Bool, _, _)], _) -> true
    | App (FinSet, [_], _) -> true
    | _ -> false

  let is_finset tp_expr = match tp_expr with
    | App (FinSet, [_], _) -> true
    | _ -> false
  let is_ghost_var vdecl = vdecl.var_ghost
  let is_const_var vdecl = vdecl.var_const
  let is_implicit_var vdecl = vdecl.var_implicit

  let is_base_type typ = (typ = int) || (typ = bool) || (typ = ref)

  let to_loc t = match t with
  | App (_, _, tp_attr) -> tp_attr.type_loc

  let to_qual_ident_exn t =
    match t with
    | App (constr, _tp_expr_list, type_attr) ->
      match constr with
      | Var qual_ident -> qual_ident
      | _ -> Error.error type_attr.type_loc "Expected type variable"

  
  let field_val = function
  | App (Fld, [val_typ], _) -> val_typ
  | _ -> failwith "Expected field type"

  let set_elem = function
  | App (Map, [elem; App (Bool, _, _)], _) -> elem
  | App (FinSet, [elem], _) -> elem
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

  type expr_ext = ..

  let compare_expr_ext (c1: expr_ext) (c2: expr_ext) = Stdlib.compare (Stdlib.Obj.tag (Stdlib.Obj.repr c1)) (Stdlib.Obj.tag (Stdlib.Obj.repr c2))

  let equal_expr_ext (c1 : expr_ext) (c2 : expr_ext) : bool =
      compare_expr_ext c1 c2 = 0

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
    | Choose
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
    | AUPred of QualIdent.t
    | AUPredCommit of QualIdent.t
    (* Variable arity operators *)
    | Setenum
    | Tuple
    | Var of QualIdent.t
    | ExprExt of expr_ext
    [@@deriving compare, equal ]

  type binder = Forall | Exists | Compr [@@deriving compare]

  type expr_attr = {
    expr_loc : location [@compare.ignore];
    expr_type : type_expr;
    (* User-written type annotation `(e: T)`, if any -- set by the parser,
       consumed (and cleared) by the type-checker, which must verify it
       against [e]'s own type and the surrounding expected type rather than
       taking it for granted. *)
    expr_type_annot : type_expr option [@compare.ignore];
  }

  and t =
    (* Application expressions *)
    | App of constr * t list * (expr_attr [@compare.ignore])
    (* Variable binder expressions *)
    | Binder of binder * var_decl list * (t list) list * t * (expr_attr [@compare.ignore]) [@@deriving compare]

  let mk_attr loc t = { expr_loc = loc; expr_type = t; expr_type_annot = None }
  let attr_of = function App (_, _, attr) | Binder (_, _, _, _, attr) -> attr
  let to_loc t = t |> attr_of |> fun attr -> attr.expr_loc
  let to_type t = t |> attr_of |> fun attr -> attr.expr_type
  let to_type_annot t = t |> attr_of |> fun attr -> attr.expr_type_annot

  let set_type t tp =
    let attr = attr_of t in
    let attr = { attr with expr_type = tp } in
    match t with
    | App (constr, expr_list, _expr_attr) -> App (constr, expr_list, attr)
    | Binder (b, v_l, trigs, expr, _expr_attr) -> Binder (b, v_l, trigs, expr, attr)

  let set_type_annot t tp_annot =
    let attr = attr_of t in
    let attr = { attr with expr_type_annot = tp_annot } in
    match t with
    | App (constr, expr_list, _expr_attr) -> App (constr, expr_list, attr)
    | Binder (b, v_l, trigs, expr, _expr_attr) -> Binder (b, v_l, trigs, expr, attr)

  let set_loc t loc =
    let attr = attr_of t in
    let attr = { attr with expr_loc = loc } in
    match t with 
    | App (constr, expr_list, _expr_attr) -> App (constr, expr_list, attr)
    | Binder (b, v_l, trigs, expr, _expr_attr) -> Binder (b, v_l, trigs, expr, attr)

  let rec set_recursive_loc loc t =
    let attr = attr_of t in
    let attr = { attr with expr_loc = loc } in
    match t with 
    | App (constr, expr_list, _expr_attr) -> 
      let expr_list = List.map expr_list ~f:(set_recursive_loc loc) in
      App (constr, expr_list, attr)
    | Binder (b, v_l, trigs, expr, _expr_attr) -> 
      let expr = set_recursive_loc loc expr in
      Binder (b, v_l, trigs, expr, attr)

  let overwrite_loc t loc = 
    if Loc.(loc = dummy) then t else (set_loc t loc)

  (** Pretty printing expressions *)

  let default_expr_ext_to_string : expr_ext -> string = fun _ -> "[ExprExt]"

  let make_constr_to_string ~expr_ext_to_string = function
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
    | Choose -> "choose"
    | And -> "&&"
    | Not -> "!"
    | Or -> "||"
    | Impl -> "==>"
    (* variables / uninterpreted symbols *)
    | Var id -> QualIdent.to_string id
    (* ownership predicates *)
    | Own -> "own"
    | AUPred id -> ("au<" ^ QualIdent.to_string id ^ ">")
    | AUPredCommit id -> ("auCommit<" ^ QualIdent.to_string id ^ ">")
    | ExprExt expr_ext -> expr_ext_to_string expr_ext

  let constr_to_string c = make_constr_to_string ~expr_ext_to_string:default_expr_ext_to_string c

  let constr_to_prio = function
    | Null | Empty | Int _ | Real _ | Bool _ -> 0
    | Setenum | Tuple | Read | Own | Choose | AUPred _ | AUPredCommit _ | Var _ | TupleLookUp | MapLookUp | MapUpdate -> 1
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
    | ExprExt expr_ext -> 18

  let to_prio = function
    | App (c, _, _) -> constr_to_prio c
    | Binder (Compr, _, _, _, _) -> 0
    | Binder ((Forall | Exists), _, _, _, _) -> 18

  let binder_to_string = function
    | Exists -> "exists"
    | Forall -> "forall"
    | Compr -> "%compr%"

  (** Builds the mutually-recursive printer family, parameterized by how to render
      [TypeExt]/[ExprExt] leaves. [make_printers] applied to the default stubs (below)
      is what every caller gets by default; an extension-aware set is built the same
      way from the extension's own hooks. *)
  let make_printers ~type_ext_to_name ~expr_ext_to_string =
    let constr_to_string = make_constr_to_string ~expr_ext_to_string in
    let (_, type_pr, _, _, _, _, type_pr_ident, _, _, _) =
      Type.make_printers ~type_ext_to_name
    in
    let module Type = struct
      include Type
      let pr = type_pr
      let pr_ident = type_pr_ident
    end in
    let rec pr_constr ppf c = Stdlib.Format.fprintf ppf "%s" (constr_to_string c)

    (* The first pr is a more verbose print which prints types of each expression. This is useful for debugging. The second pr is the normal pr which is prettier. *)
    and pr_verbose ppf e =
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
      | Binder (b, vs, trgs, e1, _) ->
          fprintf ppf "@[(%a \027[35m :%a \027[0m)@]" pr_binder (b, vs, trgs, e1, to_type e) Type.pr (to_type e)


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
          fprintf ppf "%a %a %a" pr_e1 e1 pr_constr c pr_e2 e2
      | App (Setenum, es, _) -> fprintf ppf "{|%a|}" pr_list_compact es
      | App (Tuple, es, _) -> fprintf ppf "(@[<1>%a@])" pr_list_compact es
      | App (c, es, _) -> fprintf ppf "%a(%a)" pr_constr c pr_list_compact es
      | Binder (b, vs, trgs, e1, _) ->
          fprintf ppf "%a" pr_binder (b, vs, trgs, e1, to_type e)

    and pr ppf e = pr_compact ppf e
    (* and pr ppf e = pr_verbose ppf e *)

    and pr_list ppf = Print.pr_list_comma pr ppf

    and pr_list_compact ppf = Print.pr_list_comma pr_compact ppf
    and pr_paran ppf = Stdlib.Format.fprintf ppf "(%a)" pr

    and pr_binder ppf = function
      | ((Forall | Exists) as b), vs, trgs, e, _ ->
        Stdlib.Format.fprintf ppf "%s@ %a@ ::@ %a %a" (binder_to_string b)
        pr_var_decl_list vs pr_trgs trgs pr e
      | Compr, vs, trgs, e, _ ->
          Stdlib.Format.fprintf ppf "{|@ @[%a@ ::@ %a@]@ |}" pr_var_decl_list vs
            pr e

    and pr_trgs ppf trgs =
      match trgs with
      | [] -> ()
      | trg :: trgs ->
        Stdlib.Format.fprintf ppf "{ @[%a@] } %a" (Print.pr_list_comma pr) trg pr_trgs trgs

    and pr_var_decl ppf vdecl =
      let open Type in
      Stdlib.Format.fprintf ppf "%s%s%a"
        (if vdecl.var_implicit then "implicit " else "")
        (if vdecl.var_ghost then "ghost " else "")
        Type.pr_ident
        (vdecl.var_name, vdecl.var_type)

    and pr_var_decl_list ppf = Print.pr_list_comma pr_var_decl ppf
    in
    let to_string e = Print.string_of_format pr e in
    ( pr_constr, pr_verbose, pr_compact, pr, pr_list, pr_list_compact,
      pr_paran, pr_binder, pr_trgs, pr_var_decl, pr_var_decl_list, to_string )

  let ( pr_constr, pr_verbose, pr_compact, pr, pr_list, pr_list_compact,
        pr_paran, pr_binder, pr_trgs, pr_var_decl, pr_var_decl_list, to_string ) =
    make_printers ~type_ext_to_name:Type.default_type_ext_to_name
      ~expr_ext_to_string:default_expr_ext_to_string

  (** Like [to_string], but with the freshening numbers the disambiguation pass
      gives a callable's locals dropped, so identifiers read the way they were
      written: [i(x)] rather than [i(x^24)]. For user-facing messages only --
      two distinct variables can print alike here, which is exactly why every
      other consumer wants [to_string]. *)
  let to_source_string (e : t) : string =
    let unnumber id = Ident.make (Ident.to_loc id) (Ident.name id) 0 in
    let unnumber_qi qi =
      QualIdent.make
        (List.map (QualIdent.path qi) ~f:unnumber)
        (unnumber (QualIdent.unqualify qi))
    in
    let rec go = function
      | App (constr, es, attr) ->
          let constr =
            match constr with Var qi -> Var (unnumber_qi qi) | c -> c
          in
          App (constr, List.map es ~f:go, attr)
      | Binder (b, var_decls, trgs, e, attr) ->
          let var_decls =
            List.map var_decls ~f:(fun vd ->
                Type.{ vd with var_name = unnumber vd.var_name })
          in
          Binder (b, var_decls, List.map trgs ~f:(List.map ~f:go), go e, attr)
    in
    to_string (go e)

  (** Constructors *)
  
  let mk_app ?(loc = Loc.dummy) ~typ c es =
    App (c, es, mk_attr loc typ)

  let mk_var ~typ (qual_ident: qual_ident) = 
    mk_app ~loc:(QualIdent.to_loc qual_ident) ~typ (Var qual_ident) []

  let mk_binder ?(loc = Loc.dummy) ?(typ = Type.bool) ?(trigs = []) b vs e =
    match vs with 
    | [] -> overwrite_loc e loc
    | _ -> Binder (b, vs, trigs, e, mk_attr loc typ)

  let mk_bool ?(loc = Loc.dummy) b = mk_app ~loc ~typ:Type.bool (Bool b) []

  let mk_int ?(loc = Loc.dummy) i = mk_app ~loc ~typ:Type.int (Int (Int64.of_int i)) []
  let mk_real ?(loc = Loc.dummy) r = mk_app ~loc ~typ:Type.real (Real r) []

  let mk_tuple ?(loc = Loc.dummy) es = 
    match es with
    | [e] -> overwrite_loc e loc
    | _ -> mk_app ~loc ~typ:(Type.mk_prod loc (List.map es ~f:to_type)) Tuple es

  let mk_tuple_lookup ?(loc = Loc.dummy) e i = 
    match (to_type e) with
    | App (Prod, _, _) ->
      mk_app ~loc ~typ:(Type.tuple_lookup (to_type e) i) TupleLookUp [e; mk_int ~loc i]
    | _ ->
      if i = 0 then 
        overwrite_loc e loc 
      else
        Error.error loc "Expected Tuple type"

  let mk_unit loc = mk_tuple ~loc []
  
  (** Constructor for conjunction.*)
  let mk_and ?(loc = Loc.dummy) = function
    | [] -> mk_bool ~loc true
    | [ e ] -> overwrite_loc e loc
    | es ->
        let t =
          List.fold_left es ~init:(Type.mk_bool loc) ~f:(fun t e ->
              Type.join t (to_type e))
        in
        App (And, es, mk_attr loc t)

  (* `mk_chained_and` is used in contexts where the generated expression is typechecked again.
   * This is because the typechecker only expects `&&` to be used as a binary operator,
   * for syntax reasons. Whereas, internally we allow `&&` as a k-ary operator,
   * since SMTLIB supports it.
  *)
  let mk_chained_and ?(loc = Loc.dummy) = function
  | [] -> mk_bool ~loc true
  | [ e ] -> overwrite_loc e loc
  | es ->
      let t =
        List.fold_left es ~init:(Type.mk_bool loc) ~f:(fun t e ->
            Type.join t (to_type e))
      in
      List.fold es ~init:(mk_bool true) ~f:(fun acc e ->
        App (And, [acc; e], mk_attr loc t)  
      )

  (** Constructor for disjunction.*)
  let mk_or ?(loc = Loc.dummy) = function
    | [] -> mk_bool ~loc false
    | [ e ] -> overwrite_loc e loc
    | es ->
        let t =
          List.fold_left es ~init:(Type.mk_bool loc) ~f:(fun t e ->
              Type.join t (to_type e))
        in
        App (Or, es, mk_attr loc t)

  let mk_not ?(loc = Loc.dummy) e =
    (* let t = to_type e in *)
    App (Not, [ e ], mk_attr loc Type.bool)

  let mk_null ?(loc = Loc.dummy) () =
    App (Null, [], mk_attr loc Type.ref)

  let mk_eq ?(loc = Loc.dummy) e1 e2 =
    App (Eq, [ e1; e2 ], mk_attr loc Type.bool)

  let mk_impl ?(loc = Loc.dummy) e1 e2 =
    assert (Type.equal (to_type e1) Type.bool);
    (assert ((Type.equal (to_type e2) Type.bool) || (Type.equal (to_type e2) Type.perm)));

    App (Impl, [ e1; e2 ], mk_attr loc (Type.join (to_type e1) (to_type e2)))

  let mk_ite ?(loc = Loc.dummy) e1 e2 e3 =
    assert (Type.equal (to_type e1) Type.bool);
    match e1 with
    | App (Bool b, [], _) ->
      if b then e2 else e3
    | _ ->
      App (Ite, [ e1; e2; e3 ], mk_attr loc (Type.join (to_type e2) (to_type e3)))

  let mk_maplookup ?(loc = Loc.dummy) e1 e2 =
    let t = Type.map_codom (to_type e1) in
    App (MapLookUp, [ e1; e2 ], mk_attr loc t)

  let mk_mapupdate ?(loc = Loc.dummy) e1 e2 e3 =
    let t = to_type e1 in
    App (MapUpdate, [ e1; e2; e3 ], mk_attr loc t)

  let from_var_decl (var_decl:var_decl) =
    mk_var ~typ:var_decl.var_type (QualIdent.from_ident var_decl.var_name)

  (** Auxiliary functions *)

  let to_qual_ident expr =
    match expr with
    | App (Var qual_ident, _, _) -> qual_ident
    | _ ->
      Error.error (to_loc expr)
        (Printf.sprintf "Expected Var expression instead of %s" (to_source_string expr))

  let to_ident expr =
    expr |> to_qual_ident |> QualIdent.to_ident

  let is_ident expr =
    match expr with
    | App (Var qual_ident, [], _) -> QualIdent.is_local qual_ident
    | _ -> false

  let to_int expr = 
    match expr with
    | App (Int i, _, _) -> Int.of_int64_exn i
    | _ -> Error.type_error (to_loc expr) "Expected Int constant"

  let unfold_tuple expr =
    match expr with
    | App (Tuple, es, _) -> es
    | _ -> [ expr ]

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
    | Binder (b, vars, trgs, e, expr_attr) ->
      let trgs = List.map trgs ~f:(fun exprs -> List.map exprs ~f:sub) in
      Binder (b, vars, trgs, sub e, expr_attr)
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
    | Binder (b1, vs1, trgs1, e1, _), Binder (b2, vs2, trgs2, e2, _)
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

  | Binder (binder, var_decl_list, trgs, expr, expr_attr) ->
    (* TODO: Rename the var_decl to avoid clashing with variables in the map *)
    let expr = alpha_renaming expr map in
    let trgs = List.map trgs ~f:(fun exprs -> List.map exprs ~f:(fun expr -> alpha_renaming expr map)) in
    Binder (binder, var_decl_list, trgs, expr, expr_attr)

  (** Extends [acc] with the signature of the free variables occuring in expression [e]. *)
  let signature ?(acc = Map.empty (module QualIdent)) e = 
    let rec fv bv vars = function
      | App (Var id, [],  attr) -> 
        if Set.mem bv id
        then vars
        else Map.set vars ~key:id ~data:attr.expr_type
      | App (_, ts, _) -> List.fold_left ts ~f:(fv bv) ~init:vars
      | Binder (_, vs, trgs, e, _) ->
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
      | Binder (_, vs, trgs, e, _) ->
        let syms =
          List.fold_left vs
            ~init:syms ~f:(fun syms var_decl -> Type.symbols ~acc:syms var_decl.var_type)
        in
        let bv =
          List.fold_left vs
            ~init:bv ~f:(fun bv var_decl -> Set.add bv (QualIdent.from_ident var_decl.var_name)) in
        let syms = List.fold_left trgs ~f:(fun syms exprs -> List.fold_left exprs ~f:(symbols bv) ~init:syms) ~init:syms in
        let res = symbols bv syms e in
        (*Logs.info (fun m -> m "Expr.symbols: %s" (to_string e0));
        Logs.info (fun m -> m "\nSymbols: %a" QualIdent.pr_list (Set.elements res));*)
        res
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

    | Binder (_binder, var_decl_list, trgs, expr, _expr_attr) ->
      expr_fields_accessed expr

  let rec au_preds (expr: t) : QualIdentSet.t =
    match expr with
    | App (AUPred id, _, _) -> Set.singleton (module QualIdent) id
    | App (AUPredCommit id, _, _) -> Set.singleton (module QualIdent) id
    | App (_, es, _) -> Set.union_list (module QualIdent) (List.map es ~f:au_preds)
    | Binder (_, _, _, e, _) -> au_preds e


  (** Lift quantifiers up, but only if no new quantifier alternations are introduced *)
  (*let lift_quantifiers (expr: t) : t =
      let rec merge sm zs xs ys ys2 =
        match xs, ys with
        | (x, typ1) :: xs1, (y, typ2) :: ys1 ->
          if Type.(typ1 = typ2)
          then merge (Map.add_exn ~key:x ~data:y sm) ((y, typ2) :: zs) xs1 (ys2 @ ys1) []
          else merge sm zs xs ys1 ((y, typ2) :: ys2)
        | [], _ -> sm, ys @ ys2 @ zs
        | _, [] -> 
          if List.is_empty ys2 then sm, xs @ zs
          else merge sm (List.hd_exn xs :: zs) (List.tl_exn xs) ys2 []
      in
      let rec lift_op_same loc tvs op b fs =
        let fs_same, fs_diff = List.partition_map ~f:(function
          | Binder (Exists, 
        let fs1, vs = 
          List.fold_right ~f:(fun f (fs2, vs2) ->
              let f1, vs1 = lift tvs (mk_binder b tvs f) in
              let sm, vs = merge (Map.empty (module QualIdent)) [] vs1 vs2 [] in
              subst_idents sm f1 :: fs2, vs) 
            fs ~init:([], [])
        in
        match op with
        | And -> mk_and ~loc fs1, vs
        | Or -> mk_or ~loc fs1, vs
        | _ -> assert false
      in

      and lift tvs = function e -> e
      in*)
  
  let rec existential_vars_type ?(acc = Map.empty (module Ident)) ?(pol = true) (expr: t) : Type.t IdentMap.t = 
    match expr with
    (* TODO: Biimplication? *)
    | App (Impl, [expr1; expr2], _) ->
      let acc = existential_vars_type ~acc ~pol:(not pol) expr1 in
      existential_vars_type ~acc ~pol expr2
    | App (Not, [expr], _) ->
      existential_vars_type ~acc ~pol:(not pol) expr
    | App (_, exprs, _) ->
      List.fold exprs ~init:acc ~f:(fun acc e ->
          existential_vars_type ~acc ~pol e
        )
    | Binder (b, vds, _, e, _) ->
      let acc = match b, pol with
      | Exists, true | Forall, false -> 
        List.fold vds ~init:acc ~f:(fun acc vd -> Map.set acc ~key:vd.var_name ~data:vd.var_type)
      | _ -> acc
      in
      existential_vars_type ~acc ~pol e

  let existential_vars e = existential_vars_type e |> Map.keys |> List.fold ~f:Set.add ~init:(Set.empty (module Ident))
  
  let rec supply_witnesses wtns_renam_map (expr: t) =
    let expr = alpha_renaming expr wtns_renam_map
    in
    
    let ex_var_iden_set = 
      let ex_var_iden_list = List.map (Map.keys wtns_renam_map) ~f:(fun qi -> QualIdent.to_ident qi) in

      Set.of_list (module Ident) ex_var_iden_list
    in

    match expr with
    | App (constr, exprs, expr_attr) ->
      let exprs = List.map exprs ~f:(fun e -> supply_witnesses wtns_renam_map e) in

      App (constr, exprs, expr_attr)
    
    | Binder (Exists, vds, trgs, e, expr_attr) ->
      let new_trgs = 
        List.map trgs ~f:(fun trgs -> List.map trgs ~f:(fun e -> alpha_renaming e wtns_renam_map))
      in
      let new_e = supply_witnesses wtns_renam_map e in

      Logs.debug (fun m -> m
        "Expr.supply_witnesses: old_vds: %a"
          Ident.pr_list (List.map vds ~f:(fun vd -> vd.var_name ))
      );

      Logs.debug (fun m -> m
        "Expr.supply_witnesses: ex_var_ident_set: %a"
          Ident.pr_list (Set.to_list ex_var_iden_set)
      );

      let vds = List.filter vds ~f:(fun vd -> 
        Set.for_all ex_var_iden_set ~f:(fun ex_var_ident -> not Ident.(vd.var_name = ex_var_ident))
      ) in 
      
      Logs.debug (fun m -> m
        "Expr.supply_witnesses: new_vds: %a"
          Ident.pr_list (List.map vds ~f:(fun vd -> vd.var_name ))
      );
      
      (
        match vds with 
        | [] -> new_e
        | _ -> 
        Binder (Exists, vds, new_trgs, new_e, expr_attr)
      )

    | Binder (_b, vds, trgs, e, expr_attr) ->
      let new_trgs = 
        List.map trgs ~f:(fun trgs -> List.map trgs ~f:(fun e -> alpha_renaming e wtns_renam_map))
      in
      let new_e = supply_witnesses wtns_renam_map e in
      Binder (_b, vds, new_trgs, new_e, expr_attr)
end

type expr = Expr.t


(** Whether a callable's/module's/value's correctness is checked, admitted via the
    user's own `free` keyword, or established free by the compiler (e.g. an interface
    member inherited unchanged, or a whole included file). The latter two aren't
    interchangeable: see [Rewriter.is_relaxed_lookup] for a case that must trust only
    [MachineFree], and [Module.set_unit_free] / [Typing.merge_defs] for why a
    force-freed file must not look like a user-written `free`.

    Declared here, above [Stmt], because [Stmt.var_def] already needs it. *)
type free_status =
  | NotFree
  | UserFree
  | MachineFree

let is_free = function NotFree -> false | UserFree | MachineFree -> true

(** Statements *)

module Stmt = struct
  type spec = {
    spec_form : expr;
    spec_atomic : bool;
    spec_comment : string option;
    spec_error : (qual_ident -> Loc.t -> Error.t) list;
    (* Set when this spec's [spec_form] is a formal->actual substitution instance of a
       known callable's declared clause -- i.e. a fold/unfold of a predicate body, or a
       call-site/self exhale-of-requires / inhale-of-ensures. [qual_ident] identifies the
       declaration; the [int] indexes into the conceptual list
       [call_decl_precond @ call_decl_postcond @ [body]] for that declaration (predicates
       have their body at index 0). Lets ISC translation in [HeapsExplicitTrnsl] reuse an
       already-compiled inverse function instead of minting a fresh one per occurrence. *)
    spec_source : (qual_ident * int) option;
  }

  let mk_const_spec_error error = (fun _ _ -> error)

  let spec_error_msg spec call_id loc =
    List.map ~f:(fun msg -> msg call_id loc) spec.spec_error

  (* [var_is_free] carries the full [free_status] rather than a bool because the two
     kinds of free must stay distinguishable here: `free val default: E` written by a
     user is [UserFree] and means the value is deliberately left uninterpreted, whereas
     a whole included file being force-freed is [MachineFree] and must not excuse an
     implementing module from defining the value (see [Typing.merge_defs]). *)
  type var_def = { var_decl : var_decl; var_init : expr option; var_is_free: free_status }

  type new_desc = {
    new_lhs : qual_ident;
    new_args : (qual_ident * expr option) list;
    new_is_init : bool;
  }

  type assign_desc = { assign_lhs : qual_ident list; assign_rhs : expr; assign_is_init : bool }

  type bind_desc = {
    bind_lhs : qual_ident list;
    bind_rhs : spec;
  }

  type field_read_desc = { 
    field_read_lhs : qual_ident;
    field_read_field : qual_ident;
    field_read_ref : expr;
    field_read_is_init : bool;
  }

  type field_write_desc = { 
    field_write_ref : expr;
    field_write_field : qual_ident;
    field_write_val : expr
  }

  type havoc_desc = {
    havoc_var : qual_ident;
    havoc_is_init : bool;
  }

  type cas_desc = { 
    cas_old_val : expr;
    cas_new_val : expr;
  }

  type faa_desc = {
    faa_val : expr
  }

  type xchg_desc = {
    xchg_new_val : expr
  }

  type atomic_inbuilt_kind =
    | Cas of cas_desc
    | Faa of faa_desc
    | Xchg of xchg_desc

  let atomic_inbuilt_args = function
    | Cas cs -> [cs.cas_old_val; cs.cas_new_val]
    | Faa fs -> [fs.faa_val]
    | Xchg xs -> [xs.xchg_new_val]

  let atomic_inbuilt_string = function
    | Cas _ -> "cas"
    | Faa _ -> "faa"
    | Xchg _ -> "xchg"

  type call_desc = {
    call_lhs : qual_ident list;
    call_name : qual_ident;
    call_args : expr list;
    call_is_spawn : bool;
    call_is_init : bool;
  }

  type fpu_desc = {
    fpu_ref : expr;
    fpu_field : qual_ident;
    fpu_old_val: expr option;
    fpu_new_val : expr
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

  let use_kind_to_string = function
    | Fold -> "fold"
    | Unfold -> "unfold"

  type use_desc = {
    use_kind : use_kind;
    use_name : qual_ident;
    use_args : expr list;
    use_witnesses_or_binds : (ident * expr) list;
  }

  type auaction_kind =
    | BindAU of qual_ident
    | OpenAU of { 
      token: expr; 
      proc_qi: qual_ident; 
      proc_args: expr list; 
      lhs: expr list; 
    } 
    | AbortAU of {
      token: expr;
      proc_args: expr list;
    }
    | CommitAU of {
      token: expr;
      proc_args: expr list;
      proc_rets: expr list
    }

  let auaction_kind_to_string = function
    | BindAU _ -> "bindAU"
    | OpenAU _ -> "openAU"
    | AbortAU _ -> "abortAU"
    | CommitAU _ -> "commitAU"

  type auaction_desc = {
    auaction_kind : auaction_kind;
  }
  
  type stmt_ext = ..

  (** What one extension statement costs the atomicity analysis
      ([lib/frontend/rewrites/atomicityAnalysis.ml]), which allows at most one
      atomic step while an invariant is unfolded or an atomic update is in flight.
      An extension statement is opaque there -- it is still an unlowered
      [BasicStmtExt]/[StmtExt] tag, since the analysis has to run before the
      lowering (a `cas` lowers to a read plus a conditional write, which would
      count as several steps rather than the single machine instruction it is), so
      its cost cannot be read off the statements it eventually becomes and the
      extension has to declare it. *)
  type stmt_atomicity =
    | NoStep  (** ghost: nothing an interfering thread can observe *)
    | AtomicStep  (** exactly one atomic step, e.g. `cas`/`faa` *)
    | NonAtomicStep
        (** not permitted at all while an invariant or atomic update is open *)

  (** Extension point for contract-level clauses (e.g. [decreases]) that attach to a
      callable's or loop's contract rather than to a single statement. Carried as
      [(tag * expr list)], the same shape as [StmtExt], so core code (alpha-renaming,
      symbol collection) can walk the payload without knowing what the tag means. *)
  type contract_ext = ..

  type basic_stmt_desc =
    | VarDef of var_def
    | Spec of spec_kind * spec (* x *)
    | New of new_desc
    | Assign of assign_desc (* x *)
    | Bind of bind_desc (* x *)
    | FieldRead of field_read_desc
    | FieldWrite of field_write_desc
    | Havoc of havoc_desc (* x *)
    | Call of call_desc
    | Return of expr
    | Use of use_desc
    | AUAction of auaction_desc
    | Fpu of fpu_desc
    | BasicStmtExt of (stmt_ext * expr list)
        (** Extension point for statements that don't need to carry nested statements of
            their own -- [basic_stmt_desc] has no case that does, by design. An
            extension whose custom statement needs a nested block (e.g. a proof
            obligation) must use the top-level [StmtExt] case of [stmt_desc] instead,
            which carries a self-contained [stmt_ext] value (like [contract_ext]) rather
            than being forced into this generic [(tag * expr list)] shape. *)

  type t = { stmt_desc : stmt_desc; stmt_loc : location }

  and loop_desc = {
    loop_contract : spec list;  (** the loop invariant *)
    loop_contract_ext : contract_ext list;  (** extension-defined loop contract clauses, e.g. [decreases]; each extension defines its own constructor(s) of [contract_ext], carrying whatever payload it needs (e.g. [Decreases of spec list], reusing [spec] for its error-message/location handling) *)
    loop_prebody : t;
        (** the statement executed before testing the loop condition *)
    loop_test : expr;  (** the loop condition *)
    loop_postbody : t;  (** the actual loop body *)
  }

  and cond_desc = { cond_test : expr option; cond_then : t; cond_else : t; cond_if_assumes_false : bool; }
  and block_desc = { block_body : t list; block_is_ghost: bool }

  and stmt_desc =
    | Block of block_desc
    | Basic of basic_stmt_desc
    | Loop of loop_desc
    | Cond of cond_desc
    | StmtExt of stmt_ext
        (** Self-contained extension point for whole custom statement forms that need
            nested statements of their own (e.g. `assert e with { ... }`'s proof block).
            Each extension's own constructor of [stmt_ext] carries whatever payload it
            needs directly -- the same design as [contract_ext]. *)

  (** Pretty printing statements *)

  let default_pr_basic_stmt_ext : Formatter.t -> stmt_ext -> expr list -> unit =
    fun ppf _ _ -> Stdlib.Format.fprintf ppf "@[ext]"

  let default_pr_stmt_ext : Formatter.t -> stmt_ext -> unit =
    fun ppf _ -> Stdlib.Format.fprintf ppf "@[ext]"

  let default_contract_ext_to_string : contract_ext -> string = fun _ -> "[ext]"

  (** Builds the mutually-recursive statement printer family, parameterized by how to
      render [TypeExt]/[ExprExt]/[StmtExt]/[contract_ext] leaves. *)
  let make_printers ~type_ext_to_name ~expr_ext_to_string ~pr_basic_stmt_ext ~pr_stmt_ext ~contract_ext_to_string =
    let (_, type_pr, _, _, _, _, _, _, _, _) = Type.make_printers ~type_ext_to_name in
    let module Type = struct
      include Type
      let pr = type_pr
    end in
    let (_, _, _, expr_pr, expr_pr_list, _, _, _, _, _, _, _) =
      Expr.make_printers ~type_ext_to_name ~expr_ext_to_string
    in
    let module Expr = struct
      include Expr
      let pr = expr_pr
      let pr_list = expr_pr_list
    end in
    let rec pr_var_def ppf vdef =
      let open Stdlib.Format in
      fprintf ppf "%s%s @[<2>%a@ :@ %a%a@]"
        (if Type.is_ghost_var vdef.var_decl then "ghost " else "")
        (if Type.is_const_var vdef.var_decl then "val" else "var")
        Ident.pr vdef.var_decl.var_name Type.pr vdef.var_decl.var_type
        (fun ppf -> function
          | Some e -> fprintf ppf "@ =@ %a" Expr.pr e
          | None -> ())
        vdef.var_init

    and pr_spec_list stype ppf =
      let open Stdlib.Format in
      function
      | [] -> ()
      | [ sf ] ->
          fprintf ppf "%a%s%s %a"
            (fun ppf cmnt -> match sf.spec_comment with
            | Some c -> fprintf ppf "@\n /* %s */ @\n" c
            | None -> ()) sf.spec_comment
            (if sf.spec_atomic then "atomic " else "")
            stype Expr.pr sf.spec_form
      | sf :: sfs ->
          fprintf ppf "@<0>%s%s %a@\n%a"
            (if sf.spec_atomic then "atomic " else "")
            stype Expr.pr sf.spec_form (pr_spec_list stype) sfs

    and pr_basic_stmt ppf =
      let open Stdlib.Format in
      function
      | VarDef vdef -> pr_var_def ppf vdef
      | Assign astm -> (
          match astm.assign_lhs with
          | [] -> Expr.pr ppf astm.assign_rhs
          | vs ->
              fprintf ppf "@[<2>%a@ :=@ %a@]" QualIdent.pr_list vs Expr.pr
                astm.assign_rhs)
      | Bind bstm -> (
        match bstm.bind_lhs with
        | [] -> Expr.pr ppf bstm.bind_rhs.spec_form
        | es ->
            fprintf ppf "@[<2>%a@ :|@ %a@]" QualIdent.pr_list es Expr.pr
            bstm.bind_rhs.spec_form)
      | FieldRead fr -> fprintf ppf "@[<2>%a@ :=@ %a.%a@]" QualIdent.pr fr.field_read_lhs Expr.pr fr.field_read_ref QualIdent.pr fr.field_read_field
      | FieldWrite fw -> fprintf ppf "@[<2>%a.%a@ :=@ %a@]" Expr.pr fw.field_write_ref QualIdent.pr fw.field_write_field Expr.pr fw.field_write_val
      | Havoc hvc -> fprintf ppf "@[<2>havoc@ %a%s@]" QualIdent.pr hvc.havoc_var (if hvc.havoc_is_init then " (init)" else "")
      | New nstm ->
          fprintf ppf "@[<2>%a@ :=@ new@ %a@]" QualIdent.pr nstm.new_lhs
            (Print.pr_list_comma (fun ppf -> function
              | (f, Some e) -> fprintf ppf "%a:@ %a" QualIdent.pr f Expr.pr e
              | (f, None) -> QualIdent.pr ppf f))
            nstm.new_args

      | Spec (spec_kind, sf) -> pr_spec_list (spec_kind_to_string spec_kind) ppf [ sf ]
      | Use use_desc ->
        fprintf ppf "@[<2>%s %a(@[%a@])[%a]  @]"
          (use_kind_to_string use_desc.use_kind)
          QualIdent.pr use_desc.use_name

          Expr.pr_list use_desc.use_args

          (Util.Print.pr_list_comma (fun ppf (i,e) ->
            Stdlib.Format.fprintf ppf "%a := %a"
            Ident.pr i
            Expr.pr e
          ))  use_desc.use_witnesses_or_binds


      | Return e -> fprintf ppf "@[<2>return@ %a@]" Expr.pr e
      | Call cstm -> (
          match cstm.call_lhs with
          | [] ->
              fprintf ppf "@[%s%a(@[%a@])@]" (if cstm.call_is_spawn then "spawn " else "") QualIdent.pr cstm.call_name
                Expr.pr_list cstm.call_args
          | _ ->
              fprintf ppf "@[<2>%a@ :=@ @[%a(@[%a@])@]@]" QualIdent.pr_list
                cstm.call_lhs QualIdent.pr cstm.call_name Expr.pr_list
                cstm.call_args)
      | AUAction { auaction_kind = BindAU token} ->
        fprintf ppf "@[<2>%a := %s()@]" QualIdent.pr token (auaction_kind_to_string (BindAU token))
      | AUAction { auaction_kind = OpenAU open_au_desc} ->
        fprintf ppf "@[<2>%a := %s(%a, (%a))@]" Expr.pr_list open_au_desc.lhs (auaction_kind_to_string (OpenAU open_au_desc)) Expr.pr open_au_desc.token Expr.pr_list open_au_desc.proc_args
      | AUAction { auaction_kind = CommitAU commit_au_desc as au_action} ->
        fprintf ppf "@[<2>%s(%a, (%a), (%a) )@]" (auaction_kind_to_string au_action) Expr.pr commit_au_desc.token Expr.pr_list commit_au_desc.proc_args Expr.pr_list commit_au_desc.proc_rets
      | AUAction { auaction_kind = AbortAU abort_au_desc as au_action} ->
        fprintf ppf "@[<2>%s(%a, (%a))@]" (auaction_kind_to_string au_action) Expr.pr abort_au_desc.token Expr.pr_list abort_au_desc.proc_args
      | Fpu fpu_desc -> fprintf ppf "@[<2>fpu %a.%a : %a ~> %a@]" Expr.pr fpu_desc.fpu_ref QualIdent.pr fpu_desc.fpu_field (Util.Print.pr_option Expr.pr) fpu_desc.fpu_old_val Expr.pr fpu_desc.fpu_new_val
      | BasicStmtExt (stmt_ext, exprs) -> pr_basic_stmt_ext ppf stmt_ext exprs

    and pr ppf stmt =
      let open Stdlib.Format in
      match stmt.stmt_desc with
      | Loop ldesc ->
          let pr_loop_contract_ext ppf = function
            | [] -> ()
            | exts ->
              fprintf ppf "@\n%a"
                (Print.pr_list_sep "@\n" (fun ppf ce ->
                     fprintf ppf "%s" (contract_ext_to_string ce)))
                exts
          in
          fprintf ppf "%awhile (%a)@ @,@[<2>@ @ %a%a@]@\n%a"
            (fun ppf -> function
              | { stmt_desc = Block { block_body = []; _ }; _ } -> ()
              | s -> pr ppf s)
            ldesc.loop_prebody Expr.pr ldesc.loop_test (pr_spec_list "invariant")
            ldesc.loop_contract pr_loop_contract_ext ldesc.loop_contract_ext pr ldesc.loop_postbody
      | Cond cdesc -> (
          match cdesc.cond_test, cdesc.cond_else.stmt_desc with
          | Some test, Block { block_body = []; _ } ->
              fprintf ppf "if (@[%a@]) %a" Expr.pr test pr
                cdesc.cond_then
          | Some test, _ ->
              fprintf ppf "if (@[%a@]) %a@ else@ %a" Expr.pr test pr
                cdesc.cond_then pr cdesc.cond_else
          | None, _ ->
            fprintf ppf "choose %a@ or@ %a"
              pr cdesc.cond_then pr cdesc.cond_else
        )
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
      | StmtExt stmt_ext -> pr_stmt_ext ppf stmt_ext

    and pr_block ppf stmts = Print.pr_list_nl pr ppf stmts
    in
    let to_string s = Print.string_of_format pr s in
    let print chan s = Print.print_of_format pr s chan in
    (pr_var_def, pr_spec_list, pr_basic_stmt, pr, pr_block, to_string, print)

  let (pr_var_def, pr_spec_list, pr_basic_stmt, pr, pr_block, to_string, print) =
    make_printers ~type_ext_to_name:Type.default_type_ext_to_name
      ~expr_ext_to_string:Expr.default_expr_ext_to_string
      ~pr_basic_stmt_ext:default_pr_basic_stmt_ext
      ~pr_stmt_ext:default_pr_stmt_ext
      ~contract_ext_to_string:default_contract_ext_to_string

  (** Constructors *)

  let mk_skip ~loc = { stmt_desc = Block { block_body = []; block_is_ghost = false }; stmt_loc = loc }

  let mk_block ?(ghost=false) stmts = 
    let stmts = List.concat_map stmts ~f:(function
      | { stmt_desc = Block { block_body; block_is_ghost = false }; _ } -> block_body
      | s -> [s]) in

    Block { block_body = stmts; block_is_ghost = ghost }

  let mk_block_stmt ~loc ?(ghost=false) stmts = 
    { stmt_desc = mk_block ~ghost stmts; stmt_loc = loc }

  let mk_assume_expr ~loc ?cmnt ?(spec_error = []) ?spec_source expr : t =
    let spec = { spec_form = expr; spec_atomic = false; spec_comment = cmnt; spec_error = spec_error; spec_source } in
    { stmt_desc = Basic (Spec (Assume, spec)); stmt_loc = loc }

  let mk_assume_spec ~loc ?cmnt spec : t = 
    let cmnt = 
      match cmnt, spec.spec_comment with
      | None, _ -> spec.spec_comment
      | _, None -> cmnt
      | Some cmnt, Some c -> Some (cmnt ^ "\n" ^ c)
    in
    let spec = { spec with spec_comment = cmnt } in
    { stmt_desc = Basic (Spec (Assume, spec)); stmt_loc = loc }

  let mk_inhale_expr ~loc ?cmnt ?(spec_error = []) ?spec_source expr : t =
    let spec = { spec_form = expr; spec_atomic = false; spec_comment = cmnt; spec_error = spec_error; spec_source } in
    { stmt_desc = Basic (Spec (Inhale, spec)); stmt_loc = loc }

  let mk_inhale_spec ~loc ?cmnt spec : t = 
    let cmnt = 
      match cmnt, spec.spec_comment with
      | None, _ -> spec.spec_comment
      | _, None -> cmnt
      | Some cmnt, Some c -> Some (cmnt ^ "\n" ^ c)
    in
    let spec = { spec with spec_comment = cmnt } in
    { stmt_desc = Basic (Spec (Inhale, spec)); stmt_loc = loc }

  let mk_exhale_expr ~loc ?cmnt ?(spec_error = []) ?spec_source expr : t =
    let spec = { spec_form = expr; spec_atomic = false; spec_comment = cmnt; spec_error = spec_error; spec_source } in
    { stmt_desc = Basic (Spec (Exhale, spec)); stmt_loc = loc }

  let mk_exhale_spec ~loc ?cmnt spec : t = 
    let cmnt = 
      match cmnt, spec.spec_comment with
      | None, _ -> spec.spec_comment
      | _, None -> cmnt
      | Some cmnt, Some c -> Some (cmnt ^ "\n" ^ c)
    in
    let spec = { spec with spec_comment = cmnt } in
    { stmt_desc = Basic (Spec (Exhale, spec)); stmt_loc = loc }
  
  let mk_assert_expr ~loc ?cmnt ?(spec_error = []) ?spec_source expr : t =
    let spec = { spec_form = expr; spec_atomic = false; spec_comment = cmnt; spec_error = spec_error; spec_source } in
    { stmt_desc = Basic (Spec (Assert, spec)); stmt_loc = loc }

  let mk_assert_spec ~loc ?cmnt spec : t =
    let cmnt = 
      match cmnt, spec.spec_comment with
      | None, _ -> spec.spec_comment
      | _, None -> cmnt
      | Some cmnt, Some c -> Some (cmnt ^ "\n" ^ c)
    in
    let spec = { spec with spec_comment = cmnt } in
    { stmt_desc = Basic (Spec (Assert, spec)); stmt_loc = loc }

  let mk_field_read ~loc lhs field ref =
    { stmt_desc = Basic (FieldRead {field_read_lhs = lhs; field_read_field = field; field_read_ref = ref; field_read_is_init = false}); stmt_loc = loc }

  let mk_havoc ~loc ?(is_init = false) x = { stmt_desc = Basic (Havoc { havoc_var = x; havoc_is_init = is_init }); stmt_loc = loc }

  let mk_cond ~loc ?(cond_if_assumes_false = false) test then_ else_ =
    { stmt_desc = Cond { cond_test = test; cond_then = then_; cond_else = else_; cond_if_assumes_false }; stmt_loc = loc }

  let mk_call ~loc ?(lhs=[]) name args ~is_spawn =
    let call =
      { call_lhs = lhs;
        call_name = name;
        call_args = args;
        call_is_spawn = is_spawn;
        call_is_init = false
      }
    in
    { stmt_desc = Basic (Call call); stmt_loc = loc }

  let mk_assign ~loc ?(is_init = false) lhs rhs =
    { stmt_desc = Basic (Assign { assign_lhs = lhs; assign_rhs = rhs; assign_is_init = is_init }); stmt_loc = loc }

  let mk_field_write ~loc ref field v =
    { stmt_desc = Basic (FieldWrite {field_write_ref = ref; field_write_field = field; field_write_val = v});
      stmt_loc = loc
    }
  
  let mk_return ~loc e = { stmt_desc = Basic (Return e); stmt_loc = loc }

  let mk_bind ~loc lhs rhs =
    { stmt_desc = Basic (Bind { bind_lhs = lhs; bind_rhs = rhs }); stmt_loc = loc }

  (** Auxiliary functions *)

  let mk_spec ?(atomic = false) ?cmnt ?(spec_error = []) ?spec_source e =
    {
      spec_form = e;
      spec_atomic = atomic;
      spec_comment = cmnt;
      spec_error;
      spec_source;
    }

  let to_loc s = s.stmt_loc


  let default_basic_stmt_ext_symbols : stmt_ext -> QualIdentSet.t = fun _ -> Set.empty (module QualIdent)
  let default_stmt_ext_symbols : stmt_ext -> QualIdentSet.t = fun _ -> Set.empty (module QualIdent)

  (** Extends [accessed] with the set of all symbols occuring free in [s] *)
  (** Assumes that all var_decl stmts are abstracted away during type-checking. *)
  let make_symbols ~basic_stmt_ext_symbols ~stmt_ext_symbols ?(accessed = Set.empty (module QualIdent)) (s: t) : QualIdentSet.t =
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
          if not new_desc.new_is_init then
            Set.add accesses new_desc.new_lhs
          else
            accesses

        | Assign assign_desc ->
            let accesses =
              if not assign_desc.assign_is_init then 
                List.fold assign_desc.assign_lhs ~init:accesses ~f:Set.add
              else
                accesses
            in
            scan_expr_list accesses [assign_desc.assign_rhs]
        
        | Bind bind_desc ->
          let accesses =
            List.fold bind_desc.bind_lhs ~init:accesses ~f:Set.add
          in
          scan_expr_list accesses [bind_desc.bind_rhs.spec_form]

        | FieldRead fr_desc ->
          let accesses = 
            if not fr_desc.field_read_is_init then 
              Set.add accesses fr_desc.field_read_lhs 
            else 
              accesses
          in
          scan_expr_list accesses [fr_desc.field_read_ref]

        | FieldWrite fw_desc ->
          scan_expr_list accesses [fw_desc.field_write_ref; fw_desc.field_write_val]
            
        | Havoc hvc ->
          if not hvc.havoc_is_init then
            Set.add accesses hvc.havoc_var
          else 
            accesses

        | Call call_desc ->
          (* The callee itself is a symbol this statement depends on -- without this,
             a Proc/Lemma's call graph edges (unlike a Func's, captured via ordinary
             expression application in Expr.symbols) would be entirely invisible to
             anything walking Callable.symbols, e.g. CallGraph.build's
             strongly-connected-component analysis (see lib/ast/callGraph.ml). *)
          let accesses = Set.add accesses call_desc.call_name in
          let accesses = scan_expr_list accesses call_desc.call_args in
          let accesses =
            if not call_desc.call_is_init then
              List.fold call_desc.call_lhs
                ~f:Set.add
                ~init:accesses
            else
              accesses
          in
          accesses

        | Return e ->
          Expr.symbols ~acc:accesses e
          
        | Use use_desc ->
          let accesses = scan_expr_list accesses use_desc.use_args in
          let accesses = match use_desc.use_kind with
          | Fold  ->
            scan_expr_list accesses
              (List.map use_desc.use_witnesses_or_binds ~f:(fun (i_e, wtns) -> wtns))
          | Unfold ->
            List.fold_left use_desc.use_witnesses_or_binds ~init:accesses
              ~f:(fun accesses (i_e, wtns) -> Set.add accesses (QualIdent.from_ident i_e))
          in
          accesses

        | AUAction _ -> accesses

        | Fpu fpu_desc ->
          (match fpu_desc.fpu_old_val with
          | None -> scan_expr_list accesses [fpu_desc.fpu_ref; fpu_desc.fpu_new_val]
          | Some e -> scan_expr_list accesses [fpu_desc.fpu_ref; e; fpu_desc.fpu_new_val])
        
        | BasicStmtExt (stmt_ext, expr_list) ->
          let accesses = scan_expr_list accesses expr_list in
          Set.union accesses (basic_stmt_ext_symbols stmt_ext)
        end

      | Loop l ->
        let accesses = Expr.symbols ~acc:accesses l.loop_test in
        let accesses_prebody = symbols accesses l.loop_prebody in
        symbols accesses_prebody l.loop_postbody

      | Cond c ->
        let accesses = Option.fold ~f:(fun accesses test -> Expr.symbols ~acc:accesses test) ~init:accesses c.cond_test in
        let accesses_then = symbols accesses c.cond_then in
        symbols accesses_then c.cond_else

      | StmtExt stmt_ext ->
        Set.union accesses (stmt_ext_symbols stmt_ext)
    in
    symbols accessed s

  let symbols ?accessed s =
    make_symbols ~basic_stmt_ext_symbols:default_basic_stmt_ext_symbols
      ~stmt_ext_symbols:default_stmt_ext_symbols ?accessed s

  let local_vars_accessed (s: t) : IdentSet.t =
    let sign = symbols s in
    Set.fold sign ~f:(fun locals id ->
        if QualIdent.is_qualified id
        then locals
        else Set.add locals (QualIdent.unqualify id))
      ~init:(Set.empty (module Ident))

  let default_basic_stmt_ext_local_vars_modified : stmt_ext -> expr list -> ident list = fun _ _ -> []
  let default_stmt_ext_local_vars_modified : stmt_ext -> ident list = fun _ -> []

  let make_stmt_local_vars_modified ~basic_stmt_ext_local_vars_modified ~stmt_ext_local_vars_modified (s: t) : ident list =
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
          if not new_desc.new_is_init && List.is_empty new_desc.new_lhs.qual_path then
              [new_desc.new_lhs.qual_base]
          else
            []

        | Assign assign_desc ->
          if assign_desc.assign_is_init then
            []
          else
            List.map assign_desc.assign_lhs ~f:QualIdent.unqualify
          

        | Bind bind_desc ->
          List.filter_map bind_desc.bind_lhs ~f:(fun qi -> 
            if QualIdent.is_local qi then
                Some (QualIdent.unqualify qi)
              else
                None
          )

        | FieldRead fr_desc -> 
          if not fr_desc.field_read_is_init && List.is_empty fr_desc.field_read_lhs.qual_path then
            [fr_desc.field_read_lhs.qual_base]
          else 
            []

        | FieldWrite fw_desc -> 
            []
            
        | Havoc hvc ->
          if (QualIdent.is_local hvc.havoc_var) then 
            (if not hvc.havoc_is_init then 
              [QualIdent.to_ident hvc.havoc_var] 
            else 
              []
            )
          else
            (Error.internal_error s.stmt_loc "Only local variables should be havoc-ed; caught in stmt_local_vars_modified")

        | Call call_desc ->
          if call_desc.call_is_init then
            []
          else 
            List.filter_map call_desc.call_lhs ~f:(fun qi -> 
              if List.is_empty qi.qual_path then
                Some qi.qual_base
              else
                None
            )

        | Return _ ->
          []
          
        | Use { use_kind = Unfold; use_witnesses_or_binds; _} ->
          List.map ~f:fst use_witnesses_or_binds

        | Use _ -> []

        | AUAction _ -> []

        | Fpu fpu_desc ->
          (match fpu_desc.fpu_ref with
            | App (Expr.Var qi, _, _) -> 
              if List.is_empty qi.qual_path then
                [qi.qual_base]
              else
                []
            | _ -> [])

        (* TODO: Implement an API call for vars_modified *)
        | BasicStmtExt (stmt_ext, expr_list) -> basic_stmt_ext_local_vars_modified stmt_ext expr_list
        end

      | Loop l ->
        let modified_prebody = stmt_locals_modified l.loop_prebody in
        let modified_postbody = stmt_locals_modified l.loop_postbody in
        modified_prebody @ modified_postbody

      | Cond c ->
        let modified_then = stmt_locals_modified c.cond_then in
        let modified_else = stmt_locals_modified c.cond_else in
        modified_then @ modified_else

      | StmtExt stmt_ext -> stmt_ext_local_vars_modified stmt_ext

    in

    let modifieds = stmt_locals_modified s in
    let modifieds = List.dedup_and_sort modifieds ~compare:Ident.compare in
    modifieds

  let stmt_local_vars_modified s =
    make_stmt_local_vars_modified ~basic_stmt_ext_local_vars_modified:default_basic_stmt_ext_local_vars_modified
      ~stmt_ext_local_vars_modified:default_stmt_ext_local_vars_modified s

  let stmt_local_vars_initialized (s: t) : ident list =
    let rec stmt_locals_init (s: t): ident list =
      match s.stmt_desc with
        | Block b ->
          List.concat_map b.block_body ~f:(fun s -> stmt_locals_init s)

        | Basic s1 -> 
          begin match s1 with
          (* only checking Havoc's is enough; all other _is_init stmts are preceeded by a Havoc. *)
          | Havoc hvc ->
            if (QualIdent.is_local hvc.havoc_var) then 
              (if not hvc.havoc_is_init then 
                [] 
              else 
                [QualIdent.to_ident hvc.havoc_var]
              )
            else
              (Error.internal_error s.stmt_loc "Only local variables should be havoc-ed; caught in stmt_local_vars_initialized")

          | _ -> []
          end

        | Loop l ->
          let modified_prebody = stmt_locals_init l.loop_prebody in
          let modified_postbody = stmt_locals_init l.loop_postbody in
          modified_prebody @ modified_postbody

        | Cond c ->
          let modified_then = stmt_locals_init c.cond_then in
          let modified_else = stmt_locals_init c.cond_else in
          modified_then @ modified_else

        | StmtExt _ -> []

    in

    let vars_init = stmt_locals_init s in
    let vars_init = List.dedup_and_sort vars_init ~compare:Ident.compare in
    vars_init

  let default_basic_stmt_ext_fields_accessed : stmt_ext -> expr list -> qual_ident list = fun _ _ -> []
  let default_stmt_ext_fields_accessed : stmt_ext -> qual_ident list = fun _ -> []

  (* Conservative: an unclassified extension statement is barred from an atomic
     block rather than silently costing nothing there. *)
  let default_stmt_ext_atomicity : stmt_ext -> stmt_atomicity = fun _ -> NonAtomicStep

  let make_stmt_fields_accessed ~basic_stmt_ext_fields_accessed ~stmt_ext_fields_accessed (s: t) : qual_ident list =
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
          Expr.expr_fields_accessed assign_desc.assign_rhs
        
        | Bind bind_desc ->
          Expr.expr_fields_accessed bind_desc.bind_rhs.spec_form

        | FieldRead fr_desc -> 
          [fr_desc.field_read_field]

        | FieldWrite fw_desc -> 
          [fw_desc.field_write_field]

        | Havoc _ ->
          []

        | Call call_desc ->
          Logs.debug (fun m -> m "Call stmts should not exist in the AST during stmt_fields_accessed; found: %a" pr s);
          Error.internal_error s.stmt_loc "Call stmts should not exist in the AST during stmt_fields_accessed"

        | Return _ ->
          []
          
        | Use _ ->
          []

        | AUAction _ -> []

        | Fpu fpu_desc ->
          [fpu_desc.fpu_field]
        
        (* TODO: Implement an API for fields_accessed *)
        | BasicStmtExt (stmt_ext, expr_list) -> basic_stmt_ext_fields_accessed stmt_ext expr_list
        end

      | Loop l ->
        let heaps_accessed_prebody = stmt_fields_accessed l.loop_prebody in
        let heaps_accessed_postbody = stmt_fields_accessed l.loop_postbody in
        heaps_accessed_prebody @ heaps_accessed_postbody

      | Cond c ->
        let heaps_accessed_then = stmt_fields_accessed c.cond_then in
        let heaps_accessed_else = stmt_fields_accessed c.cond_else in
        heaps_accessed_then @ heaps_accessed_else

      | StmtExt stmt_ext -> stmt_ext_fields_accessed stmt_ext

    in

    let heaps_accessed = stmt_fields_accessed s in
    let heaps_accessed = List.dedup_and_sort heaps_accessed ~compare:QualIdent.compare in
    heaps_accessed

  let stmt_fields_accessed s =
    make_stmt_fields_accessed ~basic_stmt_ext_fields_accessed:default_basic_stmt_ext_fields_accessed
      ~stmt_ext_fields_accessed:default_stmt_ext_fields_accessed s

  let stmt_au_preds_referenced (s: t) : QualIdentSet.t =
    let rec stmt_au_preds_referenced (s: t): QualIdentSet.t =
      (* Returns all AU predicates referenced in s. *)

      match s.stmt_desc with
      | Block b ->
        Set.union_list (module QualIdent) (List.map b.block_body ~f:(fun s -> stmt_au_preds_referenced s))

      | Basic s1 -> 
        begin match s1 with
        | Spec (_, s) ->
          Expr.au_preds s.spec_form

        | _ -> Set.empty (module QualIdent)

        end

      | Loop l ->
        let au_preds_referenced_prebody = stmt_au_preds_referenced l.loop_prebody in
        let au_preds_referenced_postbody = stmt_au_preds_referenced l.loop_postbody in
        Set.union au_preds_referenced_prebody au_preds_referenced_postbody

      | Cond c ->
        let au_preds_referenced_then = stmt_au_preds_referenced c.cond_then in
        let au_preds_referenced_else = stmt_au_preds_referenced c.cond_else in
        Set.union au_preds_referenced_then au_preds_referenced_else

      | StmtExt _ -> Set.empty (module QualIdent)

    in

    stmt_au_preds_referenced s
end

(** Callables *)

module Callable = struct
  type call_kind =
    | Proc | Lemma (* proc *)
    | Func | Pred | Invariant (* func *)
  [@@deriving compare]

  (** Whether a callable of this kind is, by itself, a ghost scope -- i.e. every local
      variable declared in its body is ghost regardless of an explicit `ghost` keyword
      (see [Rewriter.enter]'s [is_ghost_scope], the sole place this rule was previously
      duplicated inline, matching the pre-existing call-site rule in [Typing.ml]'s
      [process_expr]). [Func]/[Pred]/[Invariant] have no [Stmt.t] body at all
      ([call_def] is [FuncDef], not [ProcDef]), so this only has observable effect for
      [Proc]/[Lemma]. *)
  let is_ghost_kind = function
    | Lemma | Pred | Invariant -> true
    | Proc | Func -> false

  (** A mask entry [(inv_name, arg_prefix)] identifies an invariant declaration
      together with a (possibly empty) prefix of its own formal-argument list,
      taken positionally: [] means "the whole declaration, any instance";
      a full-length list means one exact instance; anything in between denotes
      the upward closure of everything chained under it. Declaration identity
      alone (the QualIdent) already gives cross-declaration apartness for
      free, so no separate namespace-token type is needed here. *)
  type mask_entry = QualIdent.t * expr list

  (* [expr] (a plain alias to [Expr.t], not itself annotated) doesn't resolve
     through ppx_compare, so this is spelled out via [Expr.compare]/
     [QualIdent.compare] directly rather than [@@deriving compare]. *)
  let compare_mask_entry ((qi1, args1) : mask_entry) ((qi2, args2) : mask_entry) : int =
    let c = QualIdent.compare qi1 qi2 in
    if c <> 0 then c else List.compare Expr.compare args1 args2

  (* A mask entry that's a syntactic prefix of another entry for the same
     declaration denotes the *same* underlying access right, described at
     two different granularities -- not two independent rights (a shorter
     prefix is the upward closure of everything a longer one would have
     needed, per [mask_entry]'s own doc comment). This is [Antichain.Make]'s
     [Ord.meet] for [mask_entry]: [None] for two entries naming different
     declarations, or two same-declaration entries that are provably (or
     just not provably) neither a prefix of the other (purely syntactic,
     [Expr.alpha_equal] position by position -- no SMT, matching how the
     rest of this mask machinery avoids the solver where it can; an
     under-approximated meet here is always safe, just narrower); otherwise
     [Some] the longer (more specific) of the two, since its region is
     already a subset of the shorter, coarser one's. This single function
     is what gives both [mask_canon] (keeping only the maximal entries --
     e.g. dropping a redundant, specific `(i, [x])` once a coarser `(i,
     [])` for the same [i] is also present, so the right can't be spent
     twice under two different descriptions) and [mask_inter] (correctly
     computing that `{(i, [])}` met with `{(i, [x])}` is `{(i, [x])}` --
     the largest thing guaranteed by *both* sides -- rather than the empty
     set a plain element-wise intersection would give, since neither side
     literally contains the other's exact entry) their correct, consistent
     behavior for free, from the single underlying partial order. *)
  let mask_entry_meet ((qi1, args1) : mask_entry) ((qi2, args2) : mask_entry) :
      mask_entry option =
    if not (QualIdent.equal qi1 qi2) then None
    else
      let is_prefix ~(shorter : expr list) ~(longer : expr list) : bool =
        List.length shorter <= List.length longer
        &&
        match
          List.for_all2 shorter (List.take longer (List.length shorter))
            ~f:Expr.alpha_equal
        with
        | Ok b -> b
        | Unequal_lengths -> false
      in
      if is_prefix ~shorter:args1 ~longer:args2 then Some (qi2, args2)
      else if is_prefix ~shorter:args2 ~longer:args1 then Some (qi1, args1)
      else None

  (* [mask_entry] embeds [expr], which has no [sexp_of_t] (see
     [Antichain]'s own doc comment for why), so [Base.Set]/[Comparator.Make]
     isn't available here -- [Antichain.Make] only needs [compare] and
     [meet]. *)
  module MaskSet = Antichain.Make (struct
    type t = mask_entry

    let compare = compare_mask_entry
    let meet = mask_entry_meet
  end)

  (** A callable's required mask: a set of [mask_entry]. Transparently a
      plain list (matching [call_decl_precond]/[call_decl_postcond] in the
      same record), so ordinary [List] operations on a [mask] value still
      work; use [mask_union]/[mask_equal] (below) rather than raw list
      concatenation/equality to keep it in canonical (sorted, deduplicated,
      maximal-elements-only, see [mask_entry_meet]) form -- see [Antichain]
      for why that matters (the mask fixpoint's convergence check relies on
      it). *)
  type mask = MaskSet.t

  let mask_canon = MaskSet.canon
  let mask_equal = MaskSet.equal
  let mask_union = MaskSet.union
  let mask_union_list = MaskSet.union_list
  let mask_inter = MaskSet.inter

  type call_decl = {
    call_decl_kind : call_kind;  (** kind of declaration *)
    call_decl_name : ident;  (** name of associated declaration *)
    call_decl_formals : var_decl list;  (** formal parameter list *)
    call_decl_returns : var_decl list;  (** return parameter list *)
    call_decl_locals : var_decl list;  (** all local variables, excluding formal parameters and return parameters *)
    call_decl_precond : Stmt.spec list;  (** precondition *)
    call_decl_postcond : Stmt.spec list;  (** postcondition *)
    call_decl_contract_ext : Stmt.contract_ext list;  (** extension-defined contract clauses, e.g. [decreases]; see [Stmt.loop_desc.loop_contract_ext] *)
    call_decl_status : free_status; (** Whether this callable's correctness is checked, admitted, or established free by the compiler -- see [free_status] *)
    call_decl_is_auto : bool; (** Indicates whether this callable is an auto lemma *)
    call_decl_needs_mask : mask option; (** Invariant mask required from this callable's caller -- computed purely from [call_decl_precond] (see [masks.ml]); also the starting mask for checking this callable's own body. *)
    call_decl_grants_mask : mask option; (** Invariant mask entries a caller is guaranteed to gain by calling this callable, regardless of what it supplies -- computed purely from [call_decl_postcond]. Used only by other callables' checking passes at their own call sites into this one. *)
    call_decl_loc : location;  (** source location of declaration *)
  }

  type call_def =
    | ProcDef of { proc_body : Stmt.t option }
    | FuncDef of { func_body : expr option }

  type t = { call_decl : call_decl; call_def : call_def }

  (** Builds the printer family, parameterized by how to render [TypeExt]/[ExprExt]/
      [StmtExt] leaves (see [Type.make_printers]/[Expr.make_printers]/
      [Stmt.make_printers], which this composes). *)
  let make_printers ~type_ext_to_name ~expr_ext_to_string ~pr_basic_stmt_ext ~pr_stmt_ext ~contract_ext_to_string =
    let (_, _, _, expr_pr, _, _, _, _, _, expr_pr_var_decl, expr_pr_var_decl_list, _) =
      Expr.make_printers ~type_ext_to_name ~expr_ext_to_string
    in
    let module Expr = struct
      include Expr
      let pr = expr_pr
      let pr_var_decl = expr_pr_var_decl
      let pr_var_decl_list = expr_pr_var_decl_list
    end in
    let (_, stmt_pr_spec_list, _, stmt_pr, _, _, _) =
      Stmt.make_printers ~type_ext_to_name ~expr_ext_to_string ~pr_basic_stmt_ext ~pr_stmt_ext ~contract_ext_to_string
    in
    let module Stmt = struct
      include Stmt
      let pr = stmt_pr
      let pr_spec_list = stmt_pr_spec_list
    end in
    let pr_call_decl_specs ppf call_decl =
      let open Stdlib.Format in
      let pr_specs stype ppf = function
        | [] -> ()
        | specs -> fprintf ppf "@\n%a" (Stmt.pr_spec_list stype) specs
      in
      let pr_contract_ext ppf = function
        | [] -> ()
        | exts ->
          fprintf ppf "@\n%a"
            (Print.pr_list_sep "@\n" (fun ppf ce ->
                 fprintf ppf "%s" (contract_ext_to_string ce)))
            exts
      in
      fprintf ppf "%a%a%a" (pr_specs "requires") call_decl.call_decl_precond
        (pr_specs "ensures") call_decl.call_decl_postcond
        pr_contract_ext call_decl.call_decl_contract_ext
    in
    let pr_call_decl has_body ppf call_decl =
      let open Stdlib.Format in
      let auto_modifier = match call_decl.call_decl_is_auto with
        | true -> "auto "
        | false -> ""
      in
      let free_modifier = match call_decl.call_decl_status with
        | NotFree -> ""
        | UserFree | MachineFree -> "free "
      in
      let kind =
        match call_decl.call_decl_kind with
        | Pred -> "pred"
        | Func -> "func"
        | Proc -> "proc"
        | Lemma -> if has_body then "lemma" else "axiom"
        | Invariant -> "inv"
      in
      let pr_returns ppf = function
        | [] -> ()
        | rs ->
            fprintf ppf "returns (@[<0>%a@])" Expr.pr_var_decl_list rs
      in
      let pr_call_locals ppf = function
        (* | [] -> () *)
        | ls ->
            fprintf ppf "@\n/*locals (@[<0>%a@])*/" Expr.pr_var_decl_list ls
      in
      let pr_mask_entries ppf mask =
        let pr_entry ppf (qi, args) =
          match args with
          | [] -> fprintf ppf "%a" QualIdent.pr qi
          | _ -> fprintf ppf "%a(%a)" QualIdent.pr qi (Print.pr_list_comma Expr.pr) args
        in
        fprintf ppf "(@[<0>%a@])" (Print.pr_list_comma pr_entry) mask
      in
      let pr_call_needs_mask ppf = function
        | None ->
          fprintf ppf "@\n/* mask: <none> */"
        | Some mask -> fprintf ppf "@\n/* needs mask: %a */" pr_mask_entries mask
      in
      let pr_call_grants_mask ppf = function
        | None -> ()
        | Some mask -> fprintf ppf "@\n/* grants mask: %a */" pr_mask_entries mask
      in
      fprintf ppf "@[<2>%s %a(%a)@;%a%a%a%a%a@]"
        (free_modifier ^ auto_modifier ^ kind)
        Ident.pr call_decl.call_decl_name
        (Print.pr_list_comma Expr.pr_var_decl) call_decl.call_decl_formals
        pr_returns call_decl.call_decl_returns
        pr_call_decl_specs call_decl
        pr_call_locals call_decl.call_decl_locals
        pr_call_needs_mask call_decl.call_decl_needs_mask
        pr_call_grants_mask call_decl.call_decl_grants_mask
    in
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
          fprintf ppf "%a%a" (pr_call_decl (Option.is_some fdef.func_body)) call_decl  (pr_fn_body Expr.pr)
            fdef.func_body
      | { call_decl; call_def = ProcDef pdef} ->
          fprintf ppf "%a%a" (pr_call_decl (Option.is_some pdef.proc_body)) call_decl (pr_proc_body Stmt.pr)
            pdef.proc_body
    in
    (pr_call_decl_specs, pr_call_decl, pr)

  let (pr_call_decl_specs, pr_call_decl, pr) =
    make_printers ~type_ext_to_name:Type.default_type_ext_to_name
      ~expr_ext_to_string:Expr.default_expr_ext_to_string
      ~pr_basic_stmt_ext:Stmt.default_pr_basic_stmt_ext
      ~pr_stmt_ext:Stmt.default_pr_stmt_ext
      ~contract_ext_to_string:Stmt.default_contract_ext_to_string

  (** Auxiliary functions *)

  let to_decl (call: t) = call.call_decl

  let to_ident (call: t) = call |> to_decl |> fun call_decl -> call_decl.call_decl_name

  let to_loc (call: t) = call |> to_decl |> fun call_decl -> call_decl.call_decl_loc

  let kind (call: t) = call |> to_decl |> fun call_decl -> call_decl.call_decl_kind

  let is_abstract = function
    | { call_def = FuncDef { func_body = None; _ }; _ }
    | { call_def = ProcDef { proc_body = None; _ }; _ } -> true
    | _ -> false
  
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
    (* Logs.debug (fun m -> m "Computing symbols for callable %a" pr callable); *)
    let symbols_w_locals =
      match callable.call_def with
      | FuncDef { func_body = Some e; _} ->
        Expr.symbols e
      | ProcDef { proc_body = Some s; _ } -> Stmt.symbols s
      | _ -> Set.empty (module QualIdent)
    in
    (* Symbols referenced only inside a [call_decl_contract_ext] entry (e.g. a helper
       function called from a `decreases` measure) are not accounted for here -- same
       pre-existing limitation as [stmt_ext], whose contribution [Stmt.symbols] also
       always treats as empty (see [default_stmt_ext_symbols]). *)
    let symbols_w_locals_and_spec =
      List.fold ~f:(fun syms spec -> Expr.symbols ~acc:syms spec.spec_form)
        ~init:symbols_w_locals
        (callable.call_decl.call_decl_precond @ callable.call_decl.call_decl_postcond)
    in

    List.fold ~f:(fun syms var_decl ->
      let qi = QualIdent.from_ident var_decl.var_name in
      (* Remove qi if it occurs but add all symbols from its type *)
      (* if Set.mem syms qi *)
      (* then (Logs.debug (fun m -> m "Removing %a from symbols" QualIdent.pr qi); *)
      (* Type.symbols ~acc:(Set.remove syms qi) var_decl.var_type) *)
      (* else (Logs.debug (fun m -> m "Adding %a to symbols" QualIdent.pr qi); *)
      Type.symbols ~acc:(Set.remove syms qi) var_decl.var_type)
      (* ) *)
      ~init:symbols_w_locals_and_spec
      (callable.call_decl.call_decl_formals @ callable.call_decl.call_decl_returns @ callable.call_decl.call_decl_locals)

  (** Change the given symbol to one whose correctness is assumed, with the given [free_status] *)
  let set_status status callable =
    let call_def =
      if is_abstract callable then callable.call_def else
        match callable.call_def with
        | ProcDef proc_def -> ProcDef { proc_body = None }
        | call_def -> call_def
    in
    { call_def; call_decl = { (to_decl callable) with call_decl_status = status } }

  let set_free callable = set_status UserFree callable
  let set_machine_free callable = set_status MachineFree callable

  let is_atomic c =
    List.exists (c.call_decl_precond @ c.call_decl_postcond) ~f:(fun spec -> spec.spec_atomic)
end


(** Modules *)

module Module = struct
  type type_def = {
    type_def_name : ident;
    type_def_expr : type_expr option;
    type_def_rep : bool;
    type_def_loc : location;
    type_def_is_free : bool;
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

  (** An argument to a functor application `F[args]`. [ModArg] names an
      existing module; [TypeArg] is a bare type (e.g. `Int`), auto-wrapped
      at type-checking time into a fresh module implementing the
      corresponding formal's rep-typed interface. *)
  type module_inst_arg =
    | ModArg of QualIdent.t
    | TypeArg of type_expr

  type module_inst = {
    mod_inst_name : ident;
    mod_inst_type : QualIdent.t;
    mod_inst_def : (QualIdent.t * module_inst_arg list) option;
    mod_inst_is_interface : bool;
    mod_inst_is_free : bool;
    mod_inst_loc : location;
  }

  type field_def = {
    field_name : ident;
    field_type : type_expr;
    field_is_ghost: bool;
    (** Set for a manifest field, `field f = M.g`, which denotes an existing
        field rather than declaring a new one -- the counterpart for fields of
        `rep type T = Int` for types. Such a field is registered as an alias in
        the symbol table, so every lookup redirects to the target and no second
        heap is created for it (heaps are keyed by field name, see
        [HeapsExplicitTrnsl.field_heap_name]). Passes that generate per-field
        artifacts must therefore skip it. *)
    field_alias : QualIdent.t option;
    field_loc : Loc.t
  }

  type module_decl = {
    mod_decl_name : ident;
    mod_decl_formals : module_inst list;
    (** Interfaces this module directly implements, in declaration order. Each
        may carry instantiation arguments, for a parameterised parent
        (`module M[A: I] : Base[A]`). Empty when nothing is declared.

        Only *direct* parents live here; [mod_decl_interfaces] holds the
        transitive closure. Parents are required to have pairwise disjoint
        ancestor sets -- see [Typing.check_parents_disjoint]. *)
    mod_decl_returns : (QualIdent.t * module_inst_arg list) list;
    mod_decl_interfaces : QualIdentSet.t;
    mod_decl_rep : ident option;
    mod_decl_is_ra : bool;
    mod_decl_is_interface : bool;
    mod_decl_status : free_status; (** See [call_decl_status]/[free_status] *)
    mod_decl_loc : location;
  }

  type import_directive = {
    import_name : qual_ident;
    import_all : bool; (* indicate whether all members of the module should be imported *)
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

  (** Builds the printer family, parameterized by how to render [TypeExt]/[ExprExt]/
      [StmtExt] leaves (see [Type.make_printers]/[Expr.make_printers]/
      [Stmt.make_printers]/[Callable.make_printers], which this composes). *)
  let make_printers ~type_ext_to_name ~expr_ext_to_string ~pr_basic_stmt_ext ~pr_stmt_ext ~contract_ext_to_string =
    let (_, type_pr, _, _, _, _, _, _, type_pr_list, _) =
      Type.make_printers ~type_ext_to_name
    in
    let module Type = struct
      include Type
      let pr = type_pr
      let pr_list = type_pr_list
    end in
    let (stmt_pr_var_def, _, _, _, _, _, _) =
      Stmt.make_printers ~type_ext_to_name ~expr_ext_to_string ~pr_basic_stmt_ext ~pr_stmt_ext ~contract_ext_to_string
    in
    let module Stmt = struct
      include Stmt
      let pr_var_def = stmt_pr_var_def
    end in
    let (_, _, callable_pr) =
      Callable.make_printers ~type_ext_to_name ~expr_ext_to_string ~pr_basic_stmt_ext ~pr_stmt_ext ~contract_ext_to_string
    in
    let module Callable = struct
      include Callable
      let pr = callable_pr
    end in
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
            | vs ->
              let pr_parent ppf (qi, args) =
                match args with
                | [] -> QualIdent.pr ppf qi
                | _ ->
                  fprintf ppf "%a[@[%a@]]" QualIdent.pr qi
                    (Print.pr_list_comma pr_mod_inst_arg) args
              in
              fprintf ppf "@ : %a" (Print.pr_list_comma pr_parent) vs)
        md.mod_decl.mod_decl_returns (* body *) pr_instr_list md.mod_def

    and pr_instr ppf =
      let open Stdlib.Format in
      function
      | SymbolDef symbol -> pr_symbol ppf symbol
      | Import { import_name = qid; import_all = all; _ } ->
        fprintf ppf "@[<2>import@ %a%s@]" QualIdent.pr qid (if all then "._" else "")

    and pr_instr_list ppf ms = Print.pr_list_sep "@\n@\n" pr_instr ppf ms

    and pr_mod_inst_arg ppf = function
      | ModArg qi -> QualIdent.pr ppf qi
      | TypeArg tp -> Type.pr ppf tp

    and pr_symbol ppf =
      let open Stdlib.Format in
      function
      | ModDef md -> pr ppf md
      | ModInst ma ->
          fprintf ppf "@[<2>%smodule@ %a : %a%a@]"
            (if ma.mod_inst_is_free then "free " else "")
            Ident.pr ma.mod_inst_name
            QualIdent.pr ma.mod_inst_type
            (fun ppf -> function
              | None -> ()
              | Some (t, ts) -> fprintf ppf " =@ %a[%a]" QualIdent.pr t (Print.pr_list_comma pr_mod_inst_arg) ts)
            ma.mod_inst_def
      | TypeDef ta ->
          fprintf ppf "@[%s%stype %a%a@]"
            (if ta.type_def_is_free then "free " else "")
            (if ta.type_def_rep then "rep " else "")
            Ident.pr ta.type_def_name
            (fun ppf -> function
              | None -> ()
              | Some t -> fprintf ppf " = %a" Type.pr t)
            ta.type_def_expr
      | ConstrDef cdef ->
        fprintf ppf "@[/* constr %a(%a): %a */@]"
          Ident.pr cdef.constr_name
          Type.pr_list (List.map cdef.constr_args ~f:(fun var_decl -> var_decl.var_type))
          Type.pr cdef.constr_return_type
      | DestrDef def ->
        fprintf ppf "@[/* destr %a(%a): %a */@]"
          Ident.pr def.destr_name
          Type.pr def.destr_arg
          Type.pr def.destr_return_type
      | FieldDef field_def ->
        let field_type = match field_def.field_type with
          | App (Fld, [typ], _) -> typ
          | typ -> typ
        in
        fprintf ppf "@[%sfield %a: %a@]"
          (if field_def.field_is_ghost then "ghost " else "")
          Ident.pr field_def.field_name Type.pr
          field_type
      | VarDef vdef -> Stmt.pr_var_def ppf vdef
      | CallDef cdef -> Callable.pr ppf cdef
    in
    (pr, pr_instr, pr_instr_list, pr_symbol)

  let (pr, pr_instr, pr_instr_list, pr_symbol) =
    make_printers ~type_ext_to_name:Type.default_type_ext_to_name
      ~expr_ext_to_string:Expr.default_expr_ext_to_string
      ~pr_basic_stmt_ext:Stmt.default_pr_basic_stmt_ext
      ~pr_stmt_ext:Stmt.default_pr_stmt_ext
      ~contract_ext_to_string:Stmt.default_contract_ext_to_string

  let to_string m = Print.string_of_format pr m
  let print chan m = Print.print_of_format pr m chan
  (*let print_verbose chan m = Print.print_of_format pr_verbose m chan*)
  let print_member_list chan ms = Print.print_of_format pr_instr_list ms chan

  (** Constructors *)

  let empty_decl =
    {
      mod_decl_name = Ident.make Loc.dummy "" 0;
      mod_decl_formals = [];
      mod_decl_returns = [];
      mod_decl_interfaces = Set.empty (module QualIdent);
      mod_decl_rep = None;
      mod_decl_loc = Loc.dummy;
      mod_decl_is_ra = false;
      mod_decl_is_interface = false;
      mod_decl_status = NotFree;
    }


  (** Auxiliary functions *)

  let to_ident m = m.mod_decl.mod_decl_name
      
  let rec find_mod (mod_defs: t list) (name: Ident.t) =
    match mod_defs with
    | [] -> Error.error Loc.dummy @@ Printf.sprintf "Module '%s' not found" (Ident.to_string name)
    | mod_def :: mod_defs ->
      if Ident.equal mod_def.mod_decl.mod_decl_name name then
        mod_def
      else
        find_mod mod_defs name

  let find_callable (call_defs: Callable.t list) (name: ident) =
    let res = List.find call_defs ~f:(fun call_def -> Ident.equal (Callable.to_decl call_def).call_decl_name name) in
    match res with
    | None -> Error.error Loc.dummy @@ Printf.sprintf "Callable '%s' not found" (Ident.to_string name)
    | Some call_def -> call_def

  let rec find_var (var_defs: Stmt.var_def list) (name: Ident.t) = 
    match var_defs with
    | [] -> Error.error Loc.dummy @@ Printf.sprintf "Variable '%s' not found" (Ident.to_string name)
    | var_def :: var_defs ->
      if Ident.equal (var_def.var_decl.var_name) name then
        var_def
      else
        find_var var_defs name

  let set_name md name =
    { md with mod_decl = { md.mod_decl with mod_decl_name = name } }

  (* These three carry a plain bool rather than the full [free_status], so they can only
     record *whether* they are free, not which kind. Deriving it from [status] rather
     than hardcoding [true] at least makes [set_symbol_status NotFree] able to clear the
     flag, which is what lets an inherited abstract member be un-freed. *)
  let rec set_symbol_status status = function
    | ModDef md -> ModDef (set_status status md)
    | CallDef cdef -> CallDef (Callable.set_status status cdef)
    | TypeDef td -> TypeDef { td with type_def_is_free = is_free status }
    | VarDef vd -> VarDef { vd with var_is_free = status }
    | ModInst mi -> ModInst { mi with mod_inst_is_free = is_free status }
    | symbol -> symbol
  and set_status status md =
    let mod_decl = { md.mod_decl with mod_decl_status = status } in
    { mod_decl; mod_def = List.map md.mod_def ~f:(fun instr ->
        match instr with
        | SymbolDef symbol -> SymbolDef (set_symbol_status status symbol)
        | _ -> instr) }

  let set_free = set_status UserFree
  let set_symbol_free = set_symbol_status UserFree
  let set_machine_free = set_status MachineFree
  let set_symbol_machine_free = set_symbol_status MachineFree

  (** Force a whole compilation unit free because the compiler said so -- the standard
      library, or an included file -- rather than because the user wrote `free`. Unlike
      [set_machine_free] this only *raises* [NotFree] to [MachineFree]: a `free` the user
      wrote inside the unit keeps its [UserFree] status, which matters because the two
      are not interchangeable when a member is inherited into an implementing module
      (see [Typing.merge_defs]). *)
  let rec set_symbol_unit_free = function
    | ModDef md -> ModDef (set_unit_free md)
    | CallDef cdef ->
        if is_free cdef.call_decl.call_decl_status then CallDef cdef
        else CallDef (Callable.set_status MachineFree cdef)
    | VarDef vd ->
        if is_free vd.var_is_free then VarDef vd
        else VarDef { vd with var_is_free = MachineFree }
    | TypeDef td -> TypeDef { td with type_def_is_free = true }
    | ModInst mi -> ModInst { mi with mod_inst_is_free = true }
    | symbol -> symbol

  and set_unit_free md =
    let mod_decl_status =
      if is_free md.mod_decl.mod_decl_status then md.mod_decl.mod_decl_status
      else MachineFree
    in
    { mod_decl = { md.mod_decl with mod_decl_status };
      mod_def =
        List.map md.mod_def ~f:(function
          | SymbolDef symbol -> SymbolDef (set_symbol_unit_free symbol)
          | instr -> instr) }
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
      | Lemma ->
        (match call_def.call_def with
        | ProcDef { proc_body = None } -> "axiom"
        | _ -> "lemma")
      | Proc -> "procedure"
      | Func -> "function"
      | Pred -> "predicate"
      | Invariant -> "invariant"

  let is_free = function
    | ModDef mod_def -> is_free mod_def.mod_decl.mod_decl_status
    | ModInst mod_inst -> mod_inst.mod_inst_is_free
    | TypeDef type_def -> type_def.type_def_is_free
    | ConstrDef cdef -> false
    | DestrDef cdef -> false
    | VarDef var_def -> is_free var_def.var_is_free
    | FieldDef field_def -> false
    | CallDef call_def -> is_free call_def.call_decl.call_decl_status

  (** Which *kind* of free a symbol is, where the representation records it. [TypeDef]
      and [ModInst] still carry a plain bool, so a `free` written on one of those is
      indistinguishable from a compiler-established one and is reported as
      [MachineFree]; nothing in the language actually writes `free type`/`free module`,
      and reporting them as machine-free is what keeps an abstract inherited type
      subject to the conformance check. *)
  let free_status = function
    | ModDef mod_def -> mod_def.mod_decl.mod_decl_status
    | CallDef call_def -> call_def.call_decl.call_decl_status
    | VarDef var_def -> var_def.var_is_free
    | ModInst mod_inst -> if mod_inst.mod_inst_is_free then MachineFree else NotFree
    | TypeDef type_def -> if type_def.type_def_is_free then MachineFree else NotFree
    | ConstrDef _ | DestrDef _ | FieldDef _ -> NotFree

  let set_free = Module.set_symbol_free

  let make_printers ~type_ext_to_name ~expr_ext_to_string ~pr_basic_stmt_ext ~pr_stmt_ext ~contract_ext_to_string =
    let (_, _, _, pr_symbol) =
      Module.make_printers ~type_ext_to_name ~expr_ext_to_string ~pr_basic_stmt_ext ~pr_stmt_ext ~contract_ext_to_string
    in
    let to_string m = Print.string_of_format pr_symbol m in
    (pr_symbol, to_string)

  let (pr, to_string) =
    make_printers ~type_ext_to_name:Type.default_type_ext_to_name
      ~expr_ext_to_string:Expr.default_expr_ext_to_string
      ~pr_basic_stmt_ext:Stmt.default_pr_basic_stmt_ext
      ~pr_stmt_ext:Stmt.default_pr_stmt_ext
      ~contract_ext_to_string:Stmt.default_contract_ext_to_string

end


module Predefs = struct
  let bindAU_ident = Ident.make Loc.dummy "bindAU" 0
  let openAU_ident = Ident.make Loc.dummy "openAU" 0
  let abortAU_ident = Ident.make Loc.dummy "abortAU" 0
  let commitAU_ident = Ident.make Loc.dummy "commitAU" 0
  let fpu_ident = Ident.make Loc.dummy "fpu" 0

  let is_qual_ident_au_cmnd qi =
    QualIdent.(qi = (QualIdent.from_ident bindAU_ident) 
      || qi = (QualIdent.from_ident openAU_ident)
      || qi = (QualIdent.from_ident abortAU_ident)
      || qi = (QualIdent.from_ident commitAU_ident)
      || qi = (QualIdent.from_ident fpu_ident))


  let lib_ident = (Ident.make Loc.dummy "Library" 0)

  let prog_ident = Ident.make Loc.dummy "$Program" 0
  let prog_qual_ident = QualIdent.from_ident prog_ident

  let lib_type_mod_ident = Ident.make Loc.dummy "Type" 0
  let lib_type_mod_qual_ident = QualIdent.from_list [lib_ident; lib_type_mod_ident]
  let lib_type_rep_type_ident = Ident.make Loc.dummy "T" 0

  let lib_list_mod_ident = Ident.make Loc.dummy "ListM" 0
  let lib_list_mod_qual_ident = QualIdent.from_list [lib_ident; lib_list_mod_ident]
  
  let lib_list_arg_mod_ident = Ident.make Loc.dummy "E" 0
  let lib_list_cons_ident = Ident.make Loc.dummy "cons" 0
  let lib_list_nil_ident = Ident.make Loc.dummy "nil" 0
  let lib_list_len_ident = Ident.make Loc.dummy "len" 0
  let lib_list_is_in_ident = Ident.make Loc.dummy "is_in" 0
  let lib_list_head_destr_ident = Ident.make Loc.dummy "hd" 0
  let lib_list_tail_destr_ident = Ident.make Loc.dummy "tl" 0

  let lib_ra_mod_qual_ident = QualIdent.from_list [lib_ident; Ident.make Loc.dummy "ResourceAlgebra" 0]

  let lib_cancellative_ra_mod_qual_ident = QualIdent.from_list [lib_ident; Ident.make Loc.dummy "CancellativeResourceAlgebra" 0]

  let lib_lattice_ra_mod_qual_ident = QualIdent.from_list [lib_ident; Ident.make Loc.dummy "LatticeResourceAlgebra" 0]

  let lib_frac_mod_qual_ident = QualIdent.from_list [lib_ident; Ident.make Loc.dummy "Frac" 0]

  let lib_frac_chunk_constr_ident = Ident.make Loc.dummy "frac_chunk" 0

  let lib_frac_chunk_destr1_ident = Ident.make Loc.dummy "frac_proj1" 0
  let lib_frac_chunk_destr2_ident = Ident.make Loc.dummy "frac_proj2" 0

  let lib_fraction_mod_ident = Ident.make Loc.dummy "Fraction" 0
  let lib_fraction_mod_qual_ident = QualIdent.from_list [lib_ident; lib_fraction_mod_ident]
  let lib_fraction_frac_constr_ident = Ident.make Loc.dummy "frac" 0

  let lib_auth_mod_qual_ident = QualIdent.from_list [lib_ident; Ident.make Loc.dummy "Auth" 0]
  
  let lib_auth_fun_ident = Ident.make Loc.dummy "auth" 0

  let lib_auth_full_fun_ident = Ident.make Loc.dummy "full" 0

  let lib_auth_frag_constr_ident = Ident.make Loc.dummy "auth_frag" 0
  
  let lib_auth_frag_destr1_ident = Ident.make Loc.dummy "af_proj1" 0
  
  let lib_agree_mod_qual_ident = QualIdent.from_list [lib_ident; Ident.make Loc.dummy "Agree" 0]

  let lib_agree_constr_ident = Ident.make Loc.dummy "agree" 0

  let lib_agree_destr1_ident = Ident.make Loc.dummy "value" 0

  let lib_countAgreeRA_mod_qual_ident = QualIdent.from_list [lib_ident; Ident.make Loc.dummy "CountAgree" 0]

  let lib_countAgreeRA_constr_ident = Ident.make Loc.dummy "count_cons" 0

  let lib_countAgreeRA_destr1_ident = Ident.make Loc.dummy "count" 0
  let lib_countAgreeRA_destr2_ident = Ident.make Loc.dummy "value" 0

  let lib_nat_mod_qual_ident = QualIdent.from_list [lib_ident; Ident.make Loc.dummy "Nat" 0]

  let lib_atomic_token_ra_mod_qual_ident = QualIdent.from_list [lib_ident; Ident.make Loc.dummy "AtomicTokenRA" 0]

  let lib_atomic_token_uncommitted_constr_ident = Ident.make Loc.dummy "au_uncommitted" 0

  let lib_atomic_token_uncommitted_destr_ident = Ident.make Loc.dummy "au_uncommit_proj1" 0

  let lib_atomic_token_committed_constr_ident = Ident.make Loc.dummy "au_committed" 0

  let lib_atomic_token_committed_destr1_ident = Ident.make Loc.dummy "au_commit_proj1" 0

  let lib_atomic_token_committed_destr2_ident = Ident.make Loc.dummy "au_commit_proj2" 0
end


let merge_prog (prog1: Module.t) (prog2: Module.t) =
  (*assert (Ident.equal prog1.mod_decl.mod_decl_name prog2.mod_decl.mod_decl_name);*)
  assert (List.is_empty prog1.mod_decl.mod_decl_formals);
  assert (List.is_empty prog2.mod_decl.mod_decl_formals);
  assert (List.is_empty prog1.mod_decl.mod_decl_returns);
  assert (List.is_empty prog2.mod_decl.mod_decl_returns);
  assert (Set.is_empty prog1.mod_decl.mod_decl_interfaces);
  assert (Set.is_empty prog2.mod_decl.mod_decl_interfaces);
  assert (Option.is_none prog1.mod_decl.mod_decl_rep);
  assert (Option.is_none prog2.mod_decl.mod_decl_rep);
  assert (not prog1.mod_decl.mod_decl_is_ra);
  assert (not prog2.mod_decl.mod_decl_is_ra);

  let mod_decl =
    {
      Module.mod_decl_name = prog1.mod_decl.mod_decl_name;
      mod_decl_formals = prog1.mod_decl.mod_decl_formals @ prog2.mod_decl.mod_decl_formals;
      mod_decl_returns = prog2.mod_decl.mod_decl_returns;
      mod_decl_interfaces = Set.union prog1.mod_decl.mod_decl_interfaces prog2.mod_decl.mod_decl_interfaces;
      mod_decl_rep = prog2.mod_decl.mod_decl_rep;
      mod_decl_is_ra = prog1.mod_decl.mod_decl_is_ra || prog2.mod_decl.mod_decl_is_ra;
      mod_decl_is_interface = prog1.mod_decl.mod_decl_is_interface || prog2.mod_decl.mod_decl_is_interface;
      mod_decl_status =
        (match prog1.mod_decl.mod_decl_status, prog2.mod_decl.mod_decl_status with
         | NotFree, _ | _, NotFree -> NotFree
         | _, status2 -> status2);
      mod_decl_loc = prog2.mod_decl.mod_decl_loc;
    }
  
  in

  let mod_def = prog1.mod_def @ prog2.mod_def in

  { Module.mod_decl; mod_def }


let empty_prog =
  let mod_decl = { Module.empty_decl with mod_decl_name = Predefs.prog_ident } in
  { Module.mod_decl; mod_def = [] }
