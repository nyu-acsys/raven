(** Symbol table data structure *)

open Base
open AstDef
open Util

let unknown_ident_error loc id =
  Error.error (QualIdent.to_loc id) ("Unknown identifier " ^ QualIdent.to_string id)

(* Substitutions for reifying aliased symbols.
   The first Boolean indicates whether the derived symbol is the result of a functor instantiation.
   The second Boolean indicates whether the derived symbol is still abstract.
 *)
type subst = bool * bool * QualIdent.subst

let is_instance (b, _, _) = b
let is_abstract (_, b, _) = b
let qid_subst (_, _, ss) = ss

(* Appended, not prepended: [QualIdent.requalify_path] applies the rules of
   [ss] in list order, left to right, threading each rule's output into the
   next -- so for a substitution added on top of an already-resolved (e.g.
   aliased/instantiated) symbol to correctly apply to whatever that existing
   chain produces, it must come after it in the list, not before. *)
let extend_subst s (b1, b2, ss) = (b1, b2, ss @ [ s ])

type entry =
  | Symbol of QualIdent.t
  | Alias of bool * QualIdent.t * QualIdent.subst
  (* Resolves straight through to the target, keeping the *target's* name.
     [Alias] cannot serve here: it records a reverse substitution so that a
     functor instance keeps reporting under its own path (`O.Inner`, not
     `Outer.Inner`), which is right for an instance but wrong for a manifest
     field, whose whole purpose is to denote the very same field -- and so to
     share its heap. [Import] resolves through without that substitution but is
     gated to the declaring scope, so it cannot be reached as `M.f` from
     outside. *)
  | Transparent of QualIdent.t
  | Import of QualIdent.t
  | Functions of { imported : bool; targets : QualIdent.t list }

type scope = {
  (* Fully qualified identifier of this scope *)
  scope_id : QualIdent.t;
  (* Indicates whether this scope is an uninstantiated module functor or interface *)
  scope_is_abstract : bool;
  (* Indicates whether this scope is a callable *)
  scope_is_local : bool;
  (* Scopes of submodules / callables *)
  scope_children : scope IdentHashtbl.t; [@hash.ignore]
  (* Symbols defined in this scope *)
  scope_entries : entry IdentHashtbl.t; [@hash.ignore]
  (* Cache that maps names (partially) qualified names to fully qualified names, relative to this scope. *)
  scope_cache : (int * (QualIdent.t * QualIdent.t * subst) list) QualIdentHashtbl.t;
      [@hash.ignore]
}
[@@deriving hash]

let get_scope_entries { scope_entries; _ } = scope_entries
let get_scope_children { scope_children; _ } = scope_children
let get_scope_cache { scope_cache; _ } = scope_cache
let get_scope_id { scope_id; _ } = scope_id

(*let is_local = function
  | Local _ -> true
  | _ -> false*)

(* An instance of a sealed functor, which outside the functor resolves to its interface. *)
type sealed_view = {
  sealed_functor : QualIdent.t;
  sealed_interface : QualIdent.t;
  (* The functor's formals, each paired with the module it is instantiated with *)
  sealed_args : (Ident.t * QualIdent.t) list;
}

type t = {
  (* Root scope *)
  tbl_root : scope;
  (* Current scope *)
  tbl_curr : scope;
  (* Stack of remaining open scopes *)
  tbl_path : scope list;
  (* Mapping from fully qualified names to the symbols that they represent *)
  tbl_symbols : Module.symbol QualIdentMap.t;
  (* Instances of sealed functors, by their fully qualified names *)
  tbl_sealed : sealed_view QualIdentMap.t;
  tbl_generation : int ref;
  (* Names probed in callable scopes, tagged with their cache generation. *)
  tbl_local_reads : int IdentHashtbl.t;
}

let entry_to_string = function
  (*| Symbol symbol ->
    begin match symbol with*)
  | Module.TypeDef tp ->
      "TypeDef("
      ^ Ident.to_string tp.type_def_name
      ^ " --> "
      ^ (match tp.type_def_expr with None -> "None" | Some tp -> Type.to_string tp)
      ^ ")"
  | CallDef call_def ->
      Printf.sprintf "CallDef(%s())" (Ident.to_string (Callable.to_ident call_def))
  | ModInst mod_inst -> "ModInst(" ^ Ident.to_string mod_inst.mod_inst_name ^ ")"
  | ModDef m -> "ModDef(" ^ Ident.to_string m.mod_decl.mod_decl_name ^ ")"
  | VarDef var_def ->
      "VarDecl("
      ^ Ident.to_string var_def.var_decl.var_name
      ^ ": "
      ^ Type.to_string var_def.var_decl.var_type
      ^ ")"
  | FieldDef field_decl ->
      "Field("
      ^ Ident.to_string field_decl.field_name
      ^ " : "
      ^ Type.to_string field_decl.field_type
      ^ ")"
  | ConstrDef data_type_constr ->
      Printf.sprintf "DataTypeConstr(%s (%s) : %s)"
        (Ident.to_string data_type_constr.constr_name)
        (Print.string_of_format Type.pr_var_decl_list data_type_constr.constr_args)
        (Type.to_string data_type_constr.constr_return_type)
  | DestrDef data_type_destr ->
      Printf.sprintf "DataTypeDestr(%s (%s) : %s)"
        (Ident.to_string data_type_destr.destr_name)
        (Type.to_string data_type_destr.destr_arg)
        (Type.to_string data_type_destr.destr_return_type)

let label_to_string label =
  match label with None -> "__" | Some iden -> Ident.to_string iden

let rec to_string tbl =
  let rec list_to_string t =
    match t with
    | [] -> " "
    | (k, v) :: ms ->
        (QualIdent.to_string k ^ " -> " ^ entry_to_string v ^ "\n") ^ list_to_string ms
  in

  match tbl with
  | [] -> "end\n\n"
  | t :: ts ->
      label_to_string (fst t)
      ^ " :: [ "
      ^ list_to_string (Map.to_alist (snd t))
      ^ " ]\n" ^ to_string ts

let create_scope qual_ident is_abstract is_local =
  {
    scope_id = qual_ident;
    scope_is_abstract = is_abstract;
    scope_is_local = is_local;
    scope_entries = Hashtbl.create (module Ident);
    scope_children = Hashtbl.create (module Ident);
    scope_cache = Hashtbl.create (module QualIdent);
  }

let create () =
  let root_id = QualIdent.from_ident (Ident.make Loc.dummy "$Root" 0) in
  let root_scope = create_scope root_id false false in
  {
    tbl_root = root_scope;
    tbl_curr = root_scope;
    tbl_path = [];
    tbl_symbols = Map.empty (module QualIdent);
    tbl_sealed = Map.empty (module QualIdent);
    tbl_generation = ref 0;
    tbl_local_reads = Hashtbl.create (module Ident);
  }

let invalidate_caches tbl = Int.incr tbl.tbl_generation

(** Reset table to the root scope *)
let reset tbl = { tbl with tbl_curr = tbl.tbl_root; tbl_path = [] }

(** Return the name of the root scope of [tbl] *)
let root_ident tbl = tbl.tbl_root.scope_id

(** Check whether current scope of [tbl] is the root scope *)
let curr_is_root tbl = List.is_empty tbl.tbl_path

(** Fully qualify [ident] relative to [scope] in [tbl]. *)
let fully_qualify ident scope tbl : QualIdent.t =
  let scope_ident = get_scope_id scope in
  if QualIdent.(scope_ident = root_ident tbl) then QualIdent.from_ident ident
  else QualIdent.append scope_ident ident

let pr_subst ppf (_, subst) =
  let open Stdlib.Format in
  fprintf ppf "[ @[%a@] ]"
    (Print.pr_list_sep ",\n" (fun ppf (a, b) ->
         fprintf ppf "%a -> %a" QualIdent.pr a QualIdent.pr (QualIdent.from_list b)))
    subst

(** Check whether [scope] is an ancestor of the current scope in [tbl]. *)
let is_ancestor scope tbl =
  let scope_id = get_scope_id scope in
  List.exists (tbl.tbl_curr :: tbl.tbl_path) ~f:(fun p ->
      QualIdent.(get_scope_id p = scope_id))

(** Resolve [name] to its fully qualified identifier relative to the current scope in
    [tbl]. *)
let resolve_candidates ?(canonical_aliases = false) ?(read_only = false) name (tbl : t) :
    (QualIdent.t * QualIdent.t * subst) list option =
  let open Option.Syntax in
  let rec go_forward inst_scopes scope subst ids =
    (* Logs.debug (fun m -> m "SymbolTbl.resolve.go_forward: scope: %a;\n tbl.tbl_path: %a;\n  ids1: [%a];\n entries: [%a]" 
      QualIdent.pr (get_scope_id scope) 
      (Util.Print.pr_list_comma QualIdent.pr) (List.map tbl.tbl_path ~f:get_scope_id)
      (Util.Print.pr_list_sep " " (Ident.pr)) ids 
      (Util.Print.pr_list_comma (Ident.pr)) (Hashtbl.keys (get_scope_entries scope))); *)

    (* Logs.debug (fun m -> m "Symbol.resolve.go_forward: tbl.curr_scope=%a; instantiated_scopes=%a" QualIdent.pr tbl.tbl_curr.scope_id (Util.Print.pr_list_comma QualIdent.pr) (Set.to_list inst_scopes)); *)
    match ids with
    | [] -> Some [ (get_scope_id scope, subst, false) ]
    | first_id :: ids1 -> (
        if
          scope.scope_is_abstract
          (* if this is a functor or interface ... *)
          && (not @@ is_ancestor scope tbl)
          &&
          (* ... then we should better be accessing its members from inside its definition ... *)
          (not @@ Set.mem inst_scopes (get_scope_id scope))
          (* ... or through one of its concrete instantiations. *)
        then None
        else
          let () =
            if scope.scope_is_local && (not canonical_aliases) && not read_only then
              Hashtbl.set tbl.tbl_local_reads ~key:first_id ~data:!(tbl.tbl_generation)
          in
          let scope_symbols = get_scope_entries scope in
          (* Logs.debug (fun m -> m "SymbolTbl.resolve.go_forward: scope_entries: %a" (Print.pr_list_comma Ident.pr) (Hashtbl.keys scope_symbols)); *)
          (* Logs.debug (fun m -> m "SymbolTbl.resolve.go_forward: ids2: %a" (Util.Print.pr_list_comma (Ident.pr))  ids); *)
          (* Logs.debug (fun m -> m "SymbolTbl.resolve.go_forward: subst: %a" (Util.Print.pr_list_comma
             (fun ppf (q1,q2) -> Stdlib.Format.fprintf ppf "%a -> %a" QualIdent.pr q1 (QualIdent.pr) (QualIdent.from_list q2) )
           ) subst); *)
          let* entry = Hashtbl.find scope_symbols first_id in
          (* Logs.debug (fun m -> m "SymbolTbl.resolve.go_forward: entry:"); *)
          match (entry, ids1) with
          | Alias (is_abstract, qual_ident, subst1), _ ->
              (* /// <- when can an alias have is_abstract?*)

              (* Logs.debug (fun m -> m "SymbolTbl.resolve.go_forward: found Alias: <%a, %a >" QualIdent.pr qual_ident (Util.Print.pr_list_comma
                 (fun ppf (q1,q2) -> Stdlib.Format.fprintf ppf "%a -> %a" QualIdent.pr q1 (QualIdent.pr) (QualIdent.from_list q2) )
               ) subst1) ; *)
              let subst_is_inst, subst_is_abstract, subst_subst = subst in
              let subst1 =
                List.map subst1 ~f:(fun (s, t) -> (QualIdent.requalify subst_subst s, t))
              in

              (* if the first argument is abstract, then it needs to be requalified. The second arg doesn't because this is taken care of by the order in which elements are added to the subst list. QualIdent.requalify will make sure the renaming on the second argument by existing substitutions happens *)

              (* let target_qual_ident = QualIdent.requalify subst qual_ident in *)
              let target_qual_ident = qual_ident in
              let new_path =
                QualIdent.requalify_path subst1
                  (QualIdent.to_list target_qual_ident @ ids1)
              in
              let target_subst =
                match subst1 with
                | []
                  when canonical_aliases && (not is_abstract)
                       && not (Map.mem tbl.tbl_sealed (fully_qualify first_id scope tbl))
                  ->
                    subst_subst
                | _ ->
                    ( target_qual_ident,
                      fully_qualify first_id scope tbl |> QualIdent.to_list )
                    :: subst_subst
              in
              let subst =
                ( subst_is_inst || (not @@ List.is_empty subst1),
                  subst_is_abstract && is_abstract,
                  subst1 @ target_subst )
              in
              let new_inst_scopes =
                if is_abstract && Set.is_empty inst_scopes then inst_scopes
                else Set.add inst_scopes target_qual_ident
              in
              (* Jump back to the root scope because the remainder of the path to be traversed has been requalified relative to target_qual_ident, which is a fully qualified id. *)
              go_forward new_inst_scopes tbl.tbl_root subst new_path
          | Transparent qual_ident, _ ->
              go_forward inst_scopes tbl.tbl_root subst
                (QualIdent.to_list qual_ident @ ids1)
          | Import qual_ident, _ ->
              (* Logs.debug (fun m -> m "SymbolTbl.resolve.go_forward: 2"); *)
              let target_qual_ident = (*QualIdent.requalify subst*) qual_ident in
              let new_path = QualIdent.to_list target_qual_ident @ ids1 in
              if is_ancestor scope tbl then
                go_forward inst_scopes tbl.tbl_root subst new_path
              else None
          | Functions { imported = false; targets }, [] ->
              Some
                (List.map targets ~f:(fun target -> (target, subst, scope.scope_is_local)))
          | Functions { imported = true; targets }, [] when is_ancestor scope tbl ->
              let resolved =
                List.filter_map targets ~f:(fun target ->
                    go_forward inst_scopes tbl.tbl_root subst (QualIdent.to_list target))
              in
              if List.is_empty resolved then None else Some (List.concat resolved)
          | Symbol qual_ident, [] ->
              (* Logs.debug (fun m -> m "SymbolTbl.resolve.go_forward: 3"); *)
              Some [ (qual_ident, subst, scope.scope_is_local) ]
          | _ ->
              (* Logs.debug (fun m -> m "SymbolTbl.resolve.go_forward: 4"); *)
              let scope_children = get_scope_children scope in
              let* cscope = Hashtbl.find scope_children first_id in
              go_forward inst_scopes cscope subst ids1)
  in
  let first_id = QualIdent.first_ident name in
  let rec go_backward is_first curr_scope path =
    let scope_cache = get_scope_cache curr_scope in
    (if is_first && not canonical_aliases then
       Hashtbl.find scope_cache name
       |> Option.bind ~f:(fun (generation, cached) ->
           if Int.equal generation !(tbl.tbl_generation) then Some cached else None)
     else None)
    |> Option.or_else () ~f:(fun _ ->
        if curr_scope.scope_is_local && (not canonical_aliases) && not read_only then
          Hashtbl.set tbl.tbl_local_reads ~key:first_id ~data:!(tbl.tbl_generation);
        let+ resolved =
          (* let exists = Hashtbl.mem (get_scope_entries curr_scope) first_id in *)
          (* Logs.debug (fun m -> m "SymbolTbl.resolve.go_backward: curr_scope: %a" QualIdent.pr (curr_scope.scope_id)); *)
          (* Logs.debug (fun m -> m "SymbolTbl.resolve.go_backward: first_id: %a" QualIdent.pr name); *)
          (* Logs.debug (fun m -> m "SymbolTbl.resolve.go_backward: scope_entries: %a" (Print.pr_list_comma Ident.pr) (Hashtbl.keys (get_scope_entries curr_scope))); *)
          (* Logs.debug (fun m -> m "SymbolTbl.resolve.go_backward: exists: %b" exists); *)
          if Hashtbl.mem (get_scope_entries curr_scope) first_id then
            let+ resolved =
              go_forward
                (Set.empty (module QualIdent))
                curr_scope
                (false, curr_scope.scope_is_abstract, [])
                (QualIdent.to_list name)
            in
            List.map resolved ~f:(fun (alias_qual_ident, subst, is_local) ->
                let _, _, subst_subst = subst in
                (* Compute resolved identifier *)
                let orig_qual_ident =
                  alias_qual_ident |> QualIdent.requalify subst_subst
                in
                (* Don't qualify orig_qual_ident if it identifies a symbol in a local scope *)
                let orig_qual_ident =
                  if is_local then
                    orig_qual_ident |> QualIdent.unqualify |> QualIdent.from_ident
                  else orig_qual_ident
                in
                (alias_qual_ident, orig_qual_ident, subst))
          else
            let* curr_scope1, path1 =
              match path with s :: ss -> Some (s, ss) | [] -> None
            in
            go_backward false curr_scope1 path1
        in
        let resolved =
          if is_first then
            match resolved with
            | [] | [ _ ] -> resolved
            | _ ->
                List.dedup_and_sort resolved ~compare:(fun (_, left, _) (_, right, _) ->
                    QualIdent.compare left right)
          else resolved
        in
        if is_first && (not canonical_aliases) && not read_only then
          Hashtbl.set scope_cache ~key:name ~data:(!(tbl.tbl_generation), resolved);
        resolved)
  in
  go_backward true tbl.tbl_curr tbl.tbl_path
  |> Option.map ~f:(fun resolved ->
      List.map resolved ~f:(fun (alias_qual_ident, orig_qual_ident, subst) ->
          ( alias_qual_ident,
            orig_qual_ident |> QualIdent.set_loc (QualIdent.to_loc name),
            subst )))

let resolve ?read_only name tbl =
  match resolve_candidates ?read_only name tbl with
  | Some [ resolved ] -> Some resolved
  | _ -> None

(** The sealed view that the module [name] resolves to, if any. *)
let find_sealed_view name tbl : sealed_view option =
  let open Option.Syntax in
  let* _, qual_ident, _ = resolve name tbl in
  Map.find tbl.tbl_sealed qual_ident

(** Reports that [name] is unknown, explaining when it names a member hidden by sealing.
*)
let unknown_member_error loc (name : QualIdent.t) (tbl : t) =
  let open Option.Syntax in
  let () =
    match resolve_candidates name tbl with
    | Some (_ :: _ :: _ as candidates) ->
        Error.type_error loc
          (Printf.sprintf "Ambiguous function name %s (%d candidates)"
             (QualIdent.to_string name) (List.length candidates))
    | _ -> ()
  in
  let hidden =
    let* prefix =
      if QualIdent.is_qualified name then Some (QualIdent.pop name) else None
    in
    let member = QualIdent.unqualify name in
    let is_member functor_ident =
      Map.mem tbl.tbl_symbols (QualIdent.append functor_ident member)
    in
    let instance_of_sealed =
      let* { sealed_functor; sealed_interface; _ } = find_sealed_view prefix tbl in
      let functor_is_sealed =
        match Map.find tbl.tbl_symbols sealed_functor with
        | Some (Module.ModDef { mod_decl = { mod_decl_is_sealed; _ }; _ }) ->
            mod_decl_is_sealed
        | _ -> false
      in
      if not (is_member sealed_functor) then None
      else if functor_is_sealed then
        Some
          (Printf.sprintf
             !"%{QualIdent} is an instance of the sealed module %{QualIdent}, which \
               exposes only the members of interface %{QualIdent}"
             prefix sealed_functor sealed_interface)
      else
        Some
          (Printf.sprintf
             !"%{QualIdent} is sealed with interface %{QualIdent} and exposes only its \
               members"
             prefix sealed_interface)
    in
    let sealed_functor () =
      let* _, functor_ident, _ = resolve prefix tbl in
      match Map.find tbl.tbl_symbols functor_ident with
      | Some
          (Module.ModDef
             {
               mod_decl =
                 { mod_decl_is_sealed = true; mod_decl_returns = [ (iface_ident, _) ]; _ };
               _;
             })
        when is_member functor_ident ->
          Some
            (Printf.sprintf
               !"%{QualIdent} is a sealed module, which exposes only the members of \
                 interface %{QualIdent}"
               prefix iface_ident)
      | _ -> None
    in
    let+ reason = Option.first_some instance_of_sealed (sealed_functor ()) in
    (member, reason)
  in
  match hidden with
  | Some (member, reason) ->
      Error.error loc
        (Printf.sprintf !"%{Ident} is not accessible here: %s" member reason)
  | None -> unknown_ident_error loc name

(** Resolve [name] relative to the current scope in [tbl] and return:
    - the fully qualified name of the associated symbol, relative to the scope where the
      symbol is declared
    - the fully qualified name of the associated symbol, relative to the scope where the
      symbol is used
    - the associated symbol, relative to the scope where the symbol is declared
    - a substitution map that maps the symbol definition to the scope where it is used. *)
let resolve_and_find ?read_only name tbl :
    (QualIdent.t * QualIdent.t * Module.symbol * subst) option =
  let open Option.Syntax in
  (* Logs.debug (fun m -> m "SymbolTbl.resolve_and_find: %a" QualIdent.pr name); *)
  let* alias_qual_ident, orig_qual_ident, subst = resolve ?read_only name tbl in

  let+ symbol = Map.find tbl.tbl_symbols alias_qual_ident in

  (* Logs.debug (fun m -> m "SymbolTbl.resolve_and_find: orig_qual_ident: %a" QualIdent.pr orig_qual_ident); *)
  (* Logs.debug (fun m -> m "SymbolTbl.resolve_and_find: alias_qual_ident: %a" QualIdent.pr alias_qual_ident); *)
  (* Logs.debug (fun m -> m "SymbolTbl.resolve_and_find: subst: %a\n" pr_subst subst); *)
  (alias_qual_ident, orig_qual_ident, symbol, subst)

let resolve_and_find_candidates name tbl =
  Option.value (resolve_candidates name tbl) ~default:[]
  |> List.filter_map ~f:(fun (alias, target, subst) ->
      Option.map (Map.find tbl.tbl_symbols alias) ~f:(fun symbol ->
          (alias, target, symbol, subst)))

(** Like [resolve_and_find] but throws an exception if [name] is not found in [tbl]. *)
let resolve_and_find_exn name (tbl : t) =
  (*Logs.debug (fun m -> m "SymbolTbl.resolve_and_find_exn: name: %a" QualIdent.pr name);
    Logs.debug (fun m -> m "SymbolTbl.resolve_and_find_exn: tbl_curr: %a" QualIdent.pr (tbl.tbl_curr.scope_id));
    Logs.debug (fun m -> m "SymbolTbl.resolve_and_find_exn: tbl_scope_children: [%a]" (Print.pr_list_comma Ident.pr) (Hashtbl.keys tbl.tbl_curr.scope_children));
    Logs.debug (fun m -> m "SymbolTbl.resolve_and_find_exn: tbl_scope_entries qualIdents: [%a]" (Print.pr_list_comma Ident.pr) (Hashtbl.keys tbl.tbl_curr.scope_entries));*)
  resolve_and_find name tbl
  |> Option.lazy_value ~default:(fun () ->
      (*Logs.debug (fun m ->
             m "SymbolTbl.resolve_and_find_exn: %a fail: tbl_curr: %a"
               QualIdent.pr name QualIdent.pr tbl.tbl_curr.scope_id);*)
      (* Logs.debug (fun m -> m "SymbolTbl.resolve_and_find_exn fail: tbl_symbols: %a" (Util.Print.pr_list_comma QualIdent.pr) (Map.keys (tbl.tbl_symbols))); *)
      unknown_member_error (QualIdent.to_loc name) name tbl)

(** Find the symbol associated with [name] relative to the current scope in [tbl]. *)
let find name tbl : (Module.symbol * subst) option =
  let open Option.Syntax in
  let* alias_qual_ident, _, subst = resolve name tbl in
  let+ symbol = Map.find tbl.tbl_symbols alias_qual_ident in
  (symbol, subst)

(** Like [find] but throws an exception if [name] is not found in [tbl]. *)
let find_exn loc name (tbl : t) =
  find name tbl
  |> Option.lazy_value ~default:(fun () -> unknown_member_error loc name tbl)

(** Enter the scope [name] from the current scope in [tbl]. *)
let enter name tbl : t option =
  let open Option.Syntax in
  let scope_children = get_scope_children tbl.tbl_curr in
  (* Logs.debug (fun m -> m "SymbolTbl.enter: name = %a; curr_scope = %a; scope_children = %a" Ident.pr name QualIdent.pr tbl.tbl_curr.scope_id (Util.Print.pr_list_comma Ident.pr) (Hashtbl.keys scope_children)); *)
  let+ scope = Hashtbl.find scope_children name in
  (* Logs.debug (fun m -> m "SymbolTbl.enter: scope=%a" QualIdent.pr scope.scope_id ); *)
  { tbl with tbl_curr = scope; tbl_path = tbl.tbl_curr :: tbl.tbl_path }

(** Enter the scope [name] from the current scope in [tbl]. *)
let enter_exn name tbl : t =
  enter name tbl
  |> Option.lazy_value ~default:(fun () ->
      Error.internal_error (Ident.to_loc name)
        (Printf.sprintf
           !"Did not find subscope %{Ident} in scope %{QualIdent}"
           name (get_scope_id tbl.tbl_curr)))

(** Exit the current scope in [tbl]. *)
let exit tbl : t =
  match tbl.tbl_path with
  | scope :: path -> { tbl with tbl_curr = scope; tbl_path = path }
  | [] -> failwith "Empty symbol table"

(** Go to the scope in [tbl] that declares the symbol associated with absolute identifier
    [name] *)
let goto name tbl : t =
  List.fold_left (QualIdent.path name) ~init:(reset tbl) ~f:(fun tbl ident ->
      enter ident tbl |> Option.value ~default:tbl)

let goto_scope scope tbl : t =
  (* Logs.debug (fun m -> m "SymbolTbl.goto_scope: scope = %a; tbl_curr=%a" QualIdent.pr scope QualIdent.pr tbl.tbl_curr.scope_id); *)
  List.fold_left (QualIdent.to_list scope) ~init:(reset tbl) ~f:(fun tbl ident ->
      match enter ident tbl with
      | Some tbl -> tbl
      | None ->
          Error.internal_error Loc.dummy
            (Stdlib.Format.asprintf
               !"SymbolTbl.goto_scope failed. Current_scope = %{QualIdent}; ident not \
                 found=%{Ident}; current_scope_children=[%a]"
               tbl.tbl_curr.scope_id ident
               (Util.Print.pr_list_comma Ident.pr)
               (Hashtbl.keys tbl.tbl_curr.scope_children)))

let add_to_map map loc key
    ?(duplicate = fun _ _ _ -> Error.redeclaration_error loc (Ident.to_string key)) data =
  match Hashtbl.add map ~key ~data with `Ok -> () | `Duplicate -> duplicate map key data

let get_scope_exn scope_name tbl : scope =
  let tbl = goto scope_name tbl in

  let scope_children = get_scope_children tbl.tbl_curr in

  Hashtbl.find_exn scope_children scope_name.qual_base

(** The raw target of an [Import] entry bound to [name]'s first identifier, without
    attempting to resolve it. A generic functor's members are imported under the functor's
    own path (see [import]) and cannot be resolved until the functor's parameters are
    known, so this is how the type checker recovers the candidate after ordinary
    resolution has failed. *)
let find_import_targets name (tbl : t) : QualIdent.t list =
  match QualIdent.to_list name with
  | [] -> []
  | first :: rest ->
      let rec go scope path =
        match Hashtbl.find (get_scope_entries scope) first with
        | Some (Import target) -> Some [ target ]
        | Some (Functions { imported = true; targets }) -> Some targets
        | Some _ -> None
        | None -> ( match path with s :: ss -> go s ss | [] -> None)
      in
      (* Substitute the target for the first identifier and keep the rest of the
         path: `Option.none` under `import Library.Option` is `Library.Option.none`,
         and a bare `some` under `import Library.Option._` is
         `Library.Option.some`. *)
      go tbl.tbl_curr tbl.tbl_path |> Option.value ~default:[]
      |> List.map ~f:(fun target -> QualIdent.from_list (QualIdent.to_list target @ rest))

let find_import_target name tbl =
  match find_import_targets name tbl with [ target ] -> Some target | _ -> None

let is_function = function
  | Module.CallDef call -> Poly.(Callable.kind call = Func)
  | _ -> false

let same_import_kind left right =
  match (left, right) with
  | Module.(ModDef _ | ModInst _), Module.(ModDef _ | ModInst _)
  | Module.VarDef _, Module.VarDef _ ->
      true
  | Module.CallDef left, Module.CallDef right ->
      Poly.(Callable.kind left = Callable.kind right)
  | _ -> String.equal (Symbol.kind left) (Symbol.kind right)

let import_binding ~loc ~name ~target ~symbol tbl =
  let function_ = is_function symbol in
  let entries = get_scope_entries tbl.tbl_curr in
  let set_entry entry =
    invalidate_caches tbl;
    Hashtbl.set entries ~key:name ~data:entry
  in
  match Hashtbl.find entries name with
  | None ->
      let entry =
        if function_ then Functions { imported = true; targets = [ target ] }
        else Import target
      in
      set_entry entry
  | Some (Functions { imported = true; targets }) when function_ ->
      let identity target =
        match resolve_candidates ~canonical_aliases:true target tbl with
        | Some [ (_, identity, _) ] -> identity
        | _ -> target
      in
      let already_imported =
        List.exists targets ~f:(fun existing -> QualIdent.equal existing target)
        || begin
          let target_identity = identity target in
          List.exists targets ~f:(fun existing ->
              QualIdent.equal (identity existing) target_identity)
        end
      in
      if not already_imported then
        let targets = List.sort (target :: targets) ~compare:QualIdent.compare in
        set_entry (Functions { imported = true; targets })
  | Some (Functions { imported = false; _ } | Symbol _ | Alias _ | Transparent _) -> ()
  | Some (Import existing) when QualIdent.equal existing target -> ()
  | Some (Import existing) when not function_ ->
      let existing_symbol =
        match resolve_and_find existing tbl with
        | Some (_, _, symbol, _) -> Some symbol
        | None -> Map.find tbl.tbl_symbols existing
      in
      begin match existing_symbol with
      | Some existing when not (same_import_kind existing symbol) ->
          Error.redeclaration_error loc (Ident.to_string name)
      | _ -> ()
      end
  | Some _ -> Error.redeclaration_error loc (Ident.to_string name)

let visible_members mdef tbl =
  match mdef.Module.mod_decl with
  | { mod_decl_is_sealed = true; mod_decl_returns = [ (interface, _) ]; _ } ->
      begin match resolve_and_find interface tbl with
      | Some (_, _, Module.ModDef interface, _) -> interface.mod_def
      | _ -> mdef.mod_def
      end
  | _ -> mdef.mod_def

(** Add an alias based on the import instruction [import_instr] *)
let import import_instr (tbl : t) : t =
  let open Module in
  let import_loc = import_instr.import_loc in
  let unresolved = import_instr.import_name in
  let imported = resolve_and_find_candidates unresolved tbl in
  let imported =
    if not (List.is_empty imported) then imported
    else
      let generic_members =
        if import_instr.import_all || QualIdent.is_local unresolved then []
        else
          match resolve_and_find (QualIdent.pop unresolved) tbl with
          | Some (alias, prefix, ModDef mdef, subst)
            when not (List.is_empty mdef.mod_decl.mod_decl_formals) ->
              let source = QualIdent.unqualify unresolved in
              List.filter_map (visible_members mdef tbl) ~f:(function
                | SymbolDef (CallDef call as symbol)
                  when is_function symbol
                       && (Ident.equal (Callable.source_ident call) source
                          || Ident.equal (Callable.to_ident call) source) ->
                    Some
                      ( alias,
                        QualIdent.append prefix (Callable.to_ident call),
                        symbol,
                        subst )
                | _ -> None)
          | _ -> []
      in
      if List.is_empty generic_members then [ resolve_and_find_exn unresolved tbl ]
      else generic_members
  in
  List.iter imported ~f:(fun (_, imported_ident, symbol, _) ->
      match (symbol, import_instr.import_all) with
      | ModDef mdef, true ->
          (* Generic members are retained for later implicit instantiation. *)
          let is_generic = not (List.is_empty mdef.mod_decl.mod_decl_formals) in
          List.iter (visible_members mdef tbl) ~f:(function
            | SymbolDef symbol ->
                let internal_name = Symbol.to_name symbol in
                let member = QualIdent.append unresolved internal_name in
                let target =
                  match resolve_and_find member tbl with
                  | Some (_, target, _, _) -> Some target
                  | None ->
                      if is_generic then
                        Some (QualIdent.append imported_ident internal_name)
                      else None
                in
                Option.iter target ~f:(fun target ->
                    import_binding ~loc:import_loc ~name:(Symbol.source_name symbol)
                      ~target ~symbol tbl)
            | _ -> ())
      | _, false ->
          import_binding ~loc:import_loc
            ~name:(QualIdent.unqualify unresolved)
            ~target:imported_ident ~symbol tbl
      | _, true -> Error.type_error import_loc "Expected module identifier");
  tbl

(** Register [ident] in the current scope as another name for [target], resolving straight
    through to it. Used for the artifacts a manifest field shares with the field it stands
    for: those are generated per field and named after it, so the alias needs one of its
    own pointing at the target's, or a name derived from the alias would denote a module
    that was never generated. *)
let add_transparent ident target tbl =
  let entries = get_scope_entries tbl.tbl_curr in
  begin match Hashtbl.find entries ident with
  | Some (Transparent existing) when QualIdent.equal existing target -> ()
  | _ ->
      invalidate_caches tbl;
      add_to_map entries (Ident.to_loc ident) ident (Transparent target)
        ~duplicate:(fun map key data -> Hashtbl.set map ~key ~data)
  end;
  tbl

(** Add [symbol] to the appropriate scope of [tbl]. Fails if [symbol] already exists in
    this scope. Appropriate scope is equal to the current scope in most cases. Except if
    [symbol] is something other than a local variable definition and current scope is a
    callable scope (determined by scope.scope_is_local), then the parent scope is used
    instead. *)
let add_symbol ?(scope : scope option = None) symbol tbl =
  let rec add symbol tbl =
    let curr_scope = tbl.tbl_curr in
    let symbol_ident = Symbol.to_name symbol in
    let symbol_loc = Symbol.to_loc symbol in

    let appropriate_scope =
      let is_symbol_var_def = match symbol with VarDef _ -> true | _ -> false in

      let scope = Option.value scope ~default:curr_scope in

      if scope.scope_is_local && not is_symbol_var_def then
        match tbl.tbl_path with [] -> tbl.tbl_root | scope :: _ -> scope
      else scope
    in

    (* A new local can affect cached resolutions only if its name was probed. *)
    let preserves_cache =
      match symbol with
      | VarDef _ when appropriate_scope.scope_is_local ->
          not
            (Option.value_map
               (Hashtbl.find tbl.tbl_local_reads symbol_ident)
               ~default:false
               ~f:(Int.equal !(tbl.tbl_generation)))
      | _ -> false
    in
    if not preserves_cache then invalidate_caches tbl;

    let symbol_qual_ident = fully_qualify symbol_ident appropriate_scope tbl in
    (*Logs.debug (fun m ->
        m "SymbolTbl.add_symbol: symbol_qual_ident: %a" QualIdent.pr
          symbol_qual_ident);*)
    let duplicate (map : entry IdentHashtbl.t) (key : Ident.t) data =
      match Hashtbl.find_exn map key with
      | Import _ | Functions { imported = true; _ } -> Hashtbl.set map ~key ~data
      | _ -> Error.redeclaration_error symbol_loc (Ident.to_string key)
    in

    match symbol with
    | CallDef call when is_function symbol ->
        let source = Callable.source_ident call in
        let entries = get_scope_entries appropriate_scope in
        let targets =
          match Hashtbl.find entries source with
          | None | Some (Import _) | Some (Functions { imported = true; _ }) -> []
          | Some (Functions { imported = false; targets }) -> targets
          | Some _ -> Error.redeclaration_error symbol_loc (Ident.to_string source)
        in
        if Map.mem tbl.tbl_symbols symbol_qual_ident then
          Error.redeclaration_error symbol_loc (Ident.to_string source);
        if not (Ident.equal source symbol_ident) then
          add_to_map entries symbol_loc symbol_ident (Symbol symbol_qual_ident) ~duplicate;
        Hashtbl.set entries ~key:source
          ~data:(Functions { imported = false; targets = symbol_qual_ident :: targets });
        let symbol_scope = create_scope symbol_qual_ident false true in
        add_to_map
          (get_scope_children appropriate_scope)
          symbol_loc symbol_ident symbol_scope;
        {
          tbl with
          tbl_symbols = Map.add_exn tbl.tbl_symbols ~key:symbol_qual_ident ~data:symbol;
        }
    (* A manifest field denotes an existing field, so it is registered as an
       alias rather than as a symbol of its own. [resolve]'s [Alias] case is
       generic over what it points at, so every lookup of this name redirects to
       the target -- which is what keeps the two sharing one heap. *)
    | FieldDef { field_alias = Some target; _ } ->
        let _, target_qual_ident, _, _ = resolve_and_find_exn target tbl in
        add_to_map
          (get_scope_entries appropriate_scope)
          symbol_loc symbol_ident (Transparent target_qual_ident) ~duplicate;
        tbl
    | ModInst mod_inst ->
        let mod_inst_qual_ident, subst, sealed =
          match mod_inst.mod_inst_def with
          | Some (mod_inst_func, mod_inst_args) -> (
              let _, mod_inst_func, mod_inst_symbol, subst1 =
                resolve_and_find_exn mod_inst_func tbl
              in
              let formals =
                match mod_inst_symbol with
                | Module.ModDef mdef ->
                    if not @@ is_instance subst1 then mdef.mod_decl.mod_decl_formals
                    else []
                | _ ->
                    Error.type_error
                      (QualIdent.to_loc mod_inst_func)
                      "Expected module identifier"
              in
              let res =
                List.map2 formals mod_inst_args ~f:(fun formal arg ->
                    let formal_id = QualIdent.append mod_inst_func formal.mod_inst_name in
                    let arg_qi =
                      match arg with
                      | Module.ModArg qi -> qi
                      | Module.TypeArg tp ->
                          Error.internal_error (Type.to_loc tp)
                            "Type argument was not resolved to a module before being \
                             declared"
                    in
                    let _, arg_qi, _arg_symbol, _arg_subst =
                      resolve_and_find_exn arg_qi tbl
                    in
                    (formal_id, QualIdent.to_list arg_qi))
              in
              match res with
              | Ok subst -> (
                  let inside_functor =
                    List.exists (tbl.tbl_curr :: tbl.tbl_path) ~f:(fun scope ->
                        QualIdent.(get_scope_id scope = mod_inst_func))
                  in
                  (* The interface the instance is a view of: that of a sealed functor,
                     or the one a sealed instance names, among those its module implements. *)
                  let sealed_iface =
                    match mod_inst_symbol with
                    | Module.ModDef
                        {
                          mod_decl =
                            { mod_decl_is_sealed = true; mod_decl_returns = [ iface ]; _ };
                          _;
                        } ->
                        Some iface
                    | Module.ModDef { mod_decl = { mod_decl_returns; _ }; _ }
                      when mod_inst.mod_inst_is_sealed ->
                        let _, named, _, _ =
                          resolve_and_find_exn mod_inst.mod_inst_type tbl
                        in
                        let found =
                          List.find mod_decl_returns ~f:(fun (iface_ident, _) ->
                              let _, iface_ident, _, _ =
                                resolve_and_find_exn iface_ident tbl
                              in
                              QualIdent.equal iface_ident named)
                        in
                        if Option.is_none found then
                          Error.type_error mod_inst.mod_inst_loc
                            (Printf.sprintf
                               !"Module %{QualIdent} does not declare that it implements \
                                 interface %{QualIdent}, so %{Ident} cannot be sealed \
                                 with it"
                               mod_inst_func mod_inst.mod_inst_type mod_inst.mod_inst_name);
                        found
                    | _ -> None
                  in
                  match sealed_iface with
                  | Some (iface_ident, iface_args)
                    when (not @@ is_instance subst1) && not inside_functor ->
                      (* Outside a sealed functor, an instance is a view of its
                         interface, applied to the functor's interface arguments. *)
                      let _, iface_ident, iface_symbol, _ =
                        resolve_and_find_exn iface_ident tbl
                      in
                      let iface_formals =
                        match iface_symbol with
                        | Module.ModDef idef -> idef.mod_decl.mod_decl_formals
                        | _ -> []
                      in
                      let iface_subst =
                        List.map2_exn iface_formals iface_args ~f:(fun formal arg ->
                            let arg_qi =
                              match arg with
                              | Module.ModArg qi -> qi
                              | Module.TypeArg tp ->
                                  Error.internal_error (Type.to_loc tp)
                                    "Interface argument of a sealed module was not \
                                     resolved to a module"
                            in
                            ( QualIdent.append iface_ident formal.mod_inst_name,
                              QualIdent.requalify subst arg_qi |> QualIdent.to_list ))
                      in
                      let sealed_args =
                        List.map subst ~f:(fun (formal_id, arg_path) ->
                            (QualIdent.unqualify formal_id, QualIdent.from_list arg_path))
                      in
                      ( iface_ident,
                        iface_subst,
                        Some
                          {
                            sealed_functor = mod_inst_func;
                            sealed_interface = iface_ident;
                            sealed_args;
                          } )
                  | _ -> (mod_inst_func, subst, None))
              | Unequal_lengths ->
                  Error.type_error
                    (QualIdent.to_loc mod_inst_func)
                    (Printf.sprintf
                       !"Module %{QualIdent} expects %d arguments"
                       mod_inst_func (List.length formals)))
          | None ->
              let _, mod_inst_type, _mod_inst_symbol, _ =
                resolve_and_find_exn mod_inst.mod_inst_type tbl
              in
              (mod_inst_type, [], None)
        in
        let is_abstract = mod_inst.mod_inst_is_interface in
        add_to_map
          (get_scope_entries appropriate_scope)
          symbol_loc symbol_ident
          (Alias (is_abstract, mod_inst_qual_ident, subst))
          ~duplicate;
        begin match sealed with
        | Some data ->
            { tbl with tbl_sealed = Map.set tbl.tbl_sealed ~key:symbol_qual_ident ~data }
        | None -> tbl
        end
    | _ -> (
        add_to_map
          (get_scope_entries appropriate_scope)
          symbol_loc symbol_ident (Symbol symbol_qual_ident) ~duplicate;
        let new_map = Map.add_exn tbl.tbl_symbols ~key:symbol_qual_ident ~data:symbol in
        let tbl = { tbl with tbl_symbols = new_map } in
        match symbol with
        | ModDef mod_def ->
            let is_abstract =
              mod_def.mod_decl.mod_decl_is_interface
              || List.length mod_def.mod_decl.mod_decl_formals > 0
            in
            let symbol_scope = create_scope symbol_qual_ident is_abstract false in
            add_to_map
              (get_scope_children appropriate_scope)
              symbol_loc symbol_ident symbol_scope;
            tbl
        | CallDef _ ->
            let symbol_scope = create_scope symbol_qual_ident false true in
            add_to_map
              (get_scope_children appropriate_scope)
              symbol_loc symbol_ident symbol_scope;
            tbl
        | _ -> tbl)
  in
  add symbol tbl

(** Update [symbol] in the current scope of [tbl]. Assumes that [symbol] is already
    present in this scope. Cached resolutions retain identities, not definitions. *)
let set_symbol symbol tbl : t =
  let symbol_ident = Symbol.to_name symbol in
  let symbol_qual_ident = fully_qualify symbol_ident tbl.tbl_curr tbl in
  (*Logs.debug (fun m ->
      m "SymbolTbl.set_symbol: symbol_qual_ident: %a" QualIdent.pr
        symbol_qual_ident);
  Logs.debug (fun m -> m "SymbolTbl.set_symbol: symbol: %a" Symbol.pr symbol);*)
  let new_map = Map.set tbl.tbl_symbols ~key:symbol_qual_ident ~data:symbol in

  (* Logs.debug (fun m -> m "SymbolTbl.set_symbol: new_map: %a" (Print.pr_list_comma QualIdent.pr) (Map.keys new_map)); *)
  { tbl with tbl_symbols = new_map }

(** Add local variable declarations [var_decls] to the current scope in [tbl]. Updates the
    symbol definition if a variable is already present. *)
let add_local_vars var_decls tbl =
  let curr_scope = tbl.tbl_curr in
  List.fold_left var_decls ~init:tbl ~f:(fun tbl var_decl ->
      let var_ident = var_decl.Type.var_name in
      let curr_entries = get_scope_entries curr_scope in
      let var_def = Module.VarDef { var_decl; var_init = None; var_is_free = NotFree } in
      match Hashtbl.find curr_entries var_ident with
      | None -> add_symbol var_def tbl
      | Some (Symbol qual_ident) ->
          let tbl_symbols = Map.set tbl.tbl_symbols ~key:qual_ident ~data:var_def in
          { tbl with tbl_symbols }
      | _ -> tbl (* a local variable can't be an alias *))
