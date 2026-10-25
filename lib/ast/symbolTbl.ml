(** Symbol table data structure *)

open Base
open AstDef
open Util

let unknown_ident_error loc id =
  Error.error (QualIdent.to_loc id) ("Unknown identifier " ^ QualIdent.to_string_user id)

(* Substitutions for reifying aliased symbols.
   The first Boolean indicates whether the derived symbol is the result of a functor instantiation.
   The second Boolean indicates whether the derived symbol is still abstract.
 *)
type subst = bool * bool * QualIdent.subst

let is_instance (b, _, _) = b
let is_abstract (_, b, _) = b
let qid_subst (_, _, ss) = ss

let has_unit_bindings bindings =
  List.exists bindings ~f:(fun (source, _) -> Module.is_unit_parameter_path source)

(* Appended, not prepended: [QualIdent.requalify_path] applies the rules of
   [ss] in list order, left to right, threading each rule's output into the
   next -- so for a substitution added on top of an already-resolved (e.g.
   aliased/instantiated) symbol to correctly apply to whatever that existing
   chain produces, it must come after it in the list, not before. *)
let extend_subst s (b1, b2, ss) = (b1, b2, ss @ [ s ])

(** A binding for this identifier itself, allowing preceding ancestor renamings. *)
let has_binding name subst =
  let _, bound =
    List.fold (qid_subst subst) ~init:(name, false)
      ~f:(fun (name, bound) ((source, _) as rule) ->
        (QualIdent.requalify [ rule ] name, bound || QualIdent.equal source name))
  in
  bound

(** Whether this module's own formals, rather than its ancestors', were bound. *)
let module_is_instantiated name (decl : Module.module_decl) subst =
  match decl.mod_decl_parameters with
  | Structure -> has_binding name subst
  (* An alias renames the owner without consuming the unit parameter. *)
  | UnitParameter -> has_binding (Module.unit_parameter_path name) subst
  | NamedParameters formals ->
      List.for_all formals ~f:(fun formal ->
          has_binding (QualIdent.append name formal.mod_inst_name) subst)

type entry =
  | Symbol of QualIdent.t
  | Alias of {
      is_abstract : bool;
      is_alias : bool;
          (** Only an explicit alias can discard its reverse owner qualification. *)
      permits_members : bool;
      target : QualIdent.t;
      substitution : QualIdent.subst;
    }
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
  (* The imports of a single member that no declaration hides yet, with their locations,
     names and targets. *)
  scope_named_imports : (Loc.t * QualIdent.t * QualIdent.t list) IdentHashtbl.t;
      [@hash.ignore]
}
[@@deriving hash]

let get_scope_entries { scope_entries; _ } = scope_entries
let get_scope_children { scope_children; _ } = scope_children
let get_scope_cache { scope_cache; _ } = scope_cache
let get_scope_named_imports { scope_named_imports; _ } = scope_named_imports
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

(* The binding of a key in a table of a scope before a change. *)
type change = Previous : 'a IdentHashtbl.t * Ident.t * 'a option -> change

(* The changes to scopes since the outermost open recovery point, latest first. *)
type journal = { mutable undo : change list; mutable open_points : int }

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
  (* The fully qualified names of the members that failed to type-check. *)
  tbl_poisoned : QualIdentSet.t;
  (* The scopes are mutable, so a recovery point undoes their changes from this. *)
  tbl_journal : journal;
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
    scope_named_imports = Hashtbl.create (module Ident);
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
    tbl_poisoned = Set.empty (module QualIdent);
    tbl_journal = { undo = []; open_points = 0 };
  }

let invalidate_caches tbl = Int.incr tbl.tbl_generation

(** Marks the member with the fully qualified name [qual_ident] as failed. *)
let poison qual_ident tbl =
  { tbl with tbl_poisoned = Set.add tbl.tbl_poisoned qual_ident }

(** Whether the fully qualified name [qual_ident] is that of a failed member, or of a
    member of one. *)
let is_poisoned qual_ident tbl =
  (not (Set.is_empty tbl.tbl_poisoned))
  && List.exists
       (List.init (List.length (QualIdent.to_list qual_ident)) ~f:(fun n -> n + 1))
       ~f:(fun n ->
         Set.mem tbl.tbl_poisoned
           (QualIdent.from_list (List.take (QualIdent.to_list qual_ident) n)))

(** Whether the unresolved [name] may refer to a failed member: its first identifier is
    the name of one. *)
let may_be_poisoned name tbl =
  let first = Ident.name (QualIdent.first_ident name) in
  Set.exists tbl.tbl_poisoned ~f:(fun poisoned ->
      String.equal first (Ident.name poisoned.qual_base))

(** Reset table to the root scope *)
let reset tbl = { tbl with tbl_curr = tbl.tbl_root; tbl_path = [] }

(** A copy of [tbl] that shares nothing mutable with it, so that what is added to either
    stays out of the other. *)
let copy tbl =
  let copies = ref [] in
  let rec copy_scope scope =
    let scope_children = Hashtbl.map scope.scope_children ~f:copy_scope in
    let copied =
      {
        scope with
        scope_entries = Hashtbl.copy scope.scope_entries;
        scope_children;
        scope_cache = Hashtbl.copy scope.scope_cache;
        scope_named_imports = Hashtbl.copy scope.scope_named_imports;
      }
    in
    copies := (scope, copied) :: !copies;
    copied
  in
  let tbl_root = copy_scope tbl.tbl_root in
  (* A scope outside the tree, such as a callable's while it is open, is copied alone. *)
  let copied scope =
    match List.find !copies ~f:(fun (old, _) -> phys_equal old scope) with
    | Some (_, copied) -> copied
    | None -> copy_scope scope
  in
  {
    tbl with
    tbl_root;
    tbl_curr = copied tbl.tbl_curr;
    tbl_path = List.map tbl.tbl_path ~f:copied;
    tbl_generation = ref !(tbl.tbl_generation);
    tbl_local_reads = Hashtbl.copy tbl.tbl_local_reads;
    tbl_journal = { undo = []; open_points = 0 };
  }

(** Return the name of the root scope of [tbl] *)
let root_ident tbl = tbl.tbl_root.scope_id

(** Records how to restore the binding of [key] in [map], a table of one of [tbl]'s
    scopes, while a recovery point is open. *)
let journal tbl map key =
  let journal = tbl.tbl_journal in
  if journal.open_points > 0 then
    journal.undo <- Previous (map, key, Hashtbl.find map key) :: journal.undo

let set_in_scope tbl map ~key ~data =
  journal tbl map key;
  Hashtbl.set map ~key ~data

let remove_from_scope tbl map key =
  journal tbl map key;
  Hashtbl.remove map key

let add_to_map tbl map loc key
    ?(duplicate = fun _ _ _ -> Error.redeclaration_error loc (Ident.to_string key)) data =
  if Hashtbl.mem map key then duplicate map key data else set_in_scope tbl map ~key ~data

(** Opens a recovery point, returning the state that [close_recovery_point] can roll the
    scopes back to. *)
let open_recovery_point tbl =
  tbl.tbl_journal.open_points <- tbl.tbl_journal.open_points + 1;
  tbl.tbl_journal.undo

(** Closes the recovery point opened at [checkpoint], undoing the changes to scopes since
    then if [rollback]. *)
let close_recovery_point ?(rollback = false) tbl checkpoint =
  let journal = tbl.tbl_journal in
  if rollback then begin
    let rec undo changes =
      if not (phys_equal changes checkpoint) then
        match changes with
        | [] -> ()
        | Previous (map, key, previous) :: changes ->
            begin match previous with
            | Some data -> Hashtbl.set map ~key ~data
            | None -> Hashtbl.remove map key
            end;
            undo changes
    in
    undo journal.undo;
    journal.undo <- checkpoint
  end;
  journal.open_points <- journal.open_points - 1;
  if journal.open_points = 0 then journal.undo <- []

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
let rec resolve_candidates ?(canonical_aliases = false)
    ?(preserve_abstract_owners = false) ?(read_only = false) name (tbl : t) :
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
          | ( Alias
                {
                  is_abstract;
                  is_alias;
                  permits_members;
                  target = qual_ident;
                  substitution = subst1;
                },
              _ ) ->
              (* /// <- when can an alias have is_abstract?*)

              (* Logs.debug (fun m -> m "SymbolTbl.resolve.go_forward: found Alias: <%a, %a >" QualIdent.pr qual_ident (Util.Print.pr_list_comma
                 (fun ppf (q1,q2) -> Stdlib.Format.fprintf ppf "%a -> %a" QualIdent.pr q1 (QualIdent.pr) (QualIdent.from_list q2) )
               ) subst1) ; *)
              let subst_is_inst, subst_is_abstract, subst_subst = subst in
              let subst1 =
                let rebased =
                  List.map subst1 ~f:(fun (s, t) ->
                      (QualIdent.requalify subst_subst s, t))
                in
                rebased
                @ List.filter subst1 ~f:(fun (source, _) ->
                    not (List.Assoc.mem rebased source ~equal:QualIdent.equal))
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
                  when canonical_aliases
                       && (is_alias
                          || not
                               (preserve_abstract_owners || has_unit_bindings subst_subst)
                          )
                       && (not is_abstract)
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
                (* Carry nested applications through their enclosing aliases. *)
                let source = fully_qualify first_id scope tbl in
                let rebased =
                  Set.fold inst_scopes ~init:inst_scopes ~f:(fun scopes instantiated ->
                      Set.add scopes
                        (QualIdent.requalify
                           [ (source, QualIdent.to_list target_qual_ident) ]
                           instantiated))
                in
                if not permits_members then rebased
                else if is_abstract && Set.is_empty inst_scopes then inst_scopes
                else Set.add rebased target_qual_ident
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
  let resolved =
    go_backward true tbl.tbl_curr tbl.tbl_path
    |> Option.map ~f:(fun resolved ->
        List.map resolved ~f:(fun (alias_qual_ident, orig_qual_ident, subst) ->
            ( alias_qual_ident,
              orig_qual_ident |> QualIdent.set_loc (QualIdent.to_loc name),
              subst )))
  in
  let has_unit_identity =
    Option.exists resolved
      ~f:(List.exists ~f:(fun (_, _, subst) -> has_unit_bindings (qid_subst subst)))
  in
  if (not canonical_aliases) && has_unit_identity then
    (* Preserve a fresh instance through aliases of its enclosing namespace. *)
    resolve_candidates ~canonical_aliases:true ~preserve_abstract_owners:true ~read_only
      name tbl
  else resolved

let resolve ?read_only name tbl =
  match resolve_candidates ?read_only name tbl with
  | Some [ resolved ] -> Some resolved
  | _ -> None

(** The sealed view that the module [name] resolves to, if any. *)
let find_sealed_view name tbl : sealed_view option =
  let open Option.Syntax in
  let* _, qual_ident, _ = resolve name tbl in
  match Map.find tbl.tbl_sealed qual_ident with
  | Some view -> Some view
  | None when QualIdent.is_qualified qual_ident ->
      let* parent, _, subst = resolve (QualIdent.pop qual_ident) tbl in
      let* view =
        Map.find tbl.tbl_sealed (QualIdent.append parent (QualIdent.unqualify qual_ident))
      in
      let requalify = QualIdent.requalify (qid_subst subst) in
      Some
        {
          sealed_functor = requalify view.sealed_functor;
          sealed_interface = requalify view.sealed_interface;
          sealed_args =
            List.map view.sealed_args ~f:(fun (formal, actual) ->
                (formal, requalify actual));
        }
  | None -> None

(** Reports that [name] is unknown, explaining when it names a member hidden by sealing.
*)
let unknown_member_error loc (name : QualIdent.t) (tbl : t) =
  let open Option.Syntax in
  (* A failed member is not declared; its error is already reported. *)
  if may_be_poisoned name tbl then Error.fail_with [];
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

(** Application provenance does not identify a sealed view with its implementation. *)
let application_origin name tbl =
  let open Option.Syntax in
  let binding name =
    match Map.find tbl.tbl_symbols name with
    | Some (Module.ModInst binding) -> Some (binding, Fn.id)
    | _ when QualIdent.is_qualified name ->
        let* _, _, parent, subst = resolve_and_find (QualIdent.pop name) tbl in
        begin match parent with
        | Module.ModDef parent ->
            let+ binding =
              List.find_map parent.mod_def ~f:(function
                | Module.SymbolDef (ModInst binding)
                  when Ident.equal binding.mod_inst_name (QualIdent.unqualify name) ->
                    Some binding
                | _ -> None)
            in
            (binding, QualIdent.requalify (qid_subst subst))
        | _ -> None
        end
    | _ -> None
  in
  let rec origin visited name =
    if Set.mem visited name then None
    else
      let visited = Set.add visited name in
      match find_sealed_view name tbl with
      | Some view -> Some (view.sealed_functor, view.sealed_args)
      | None ->
          begin match binding name with
          | Some ({ mod_inst_def = Some (Alias target); _ }, requalify) ->
              origin visited (requalify target)
          | Some
              ( {
                  mod_inst_def = Some (Apply (head, args) | CanonicalApply (head, args));
                  _;
                },
                requalify ) ->
              let head = requalify head in
              let* _, head, symbol, _ = resolve_and_find head tbl in
              begin match symbol with
              | Module.ModDef module_ ->
                  begin match List.zip (Module.formals module_.mod_decl) args with
                  | Unequal_lengths -> None
                  | Ok pairs ->
                      let+ arguments =
                        Option.all
                          (List.map pairs ~f:(fun (formal, argument) ->
                               match argument with
                               | Module.ModArg actual ->
                                   Some (formal.mod_inst_name, requalify actual)
                               | Module.TypeArg _ -> None))
                      in
                      (head, arguments)
                  end
              | _ -> None
              end
          | Some ({ mod_inst_def = Some (ApplyUnit head); _ }, requalify) ->
              let+ _, head, _, _ = resolve_and_find (requalify head) tbl in
              (head, [])
          | Some ({ mod_inst_def = None; _ }, _) | None ->
              let* _, target, _ = resolve name tbl in
              if QualIdent.equal name target then None else origin visited target
          end
  in
  origin (Set.empty (module QualIdent)) name

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

(** The symbol that [target] denotes, through aliases. *)
let identity ?(preserve_abstract_owners = false) target tbl =
  match
    resolve_candidates ~canonical_aliases:true ~preserve_abstract_owners target tbl
  with
  | Some [ (_, identity, _) ] -> identity
  | _ -> target

(** Whether one of [targets] and one of [declared] denote the same symbol. *)
let denote_same targets declared tbl =
  let identities qis = List.map qis ~f:(fun qi -> identity qi tbl) in
  List.exists (identities declared)
    ~f:(List.mem (identities targets) ~equal:QualIdent.equal)

let warn_hidden_import ~diagnostics ~import_loc ~import_name ~decl_loc =
  Diagnostics.warning diagnostics import_loc
    (Printf.sprintf
       !"This import of %{QualIdent} is hidden by the declaration of %{Ident} on line %d"
       import_name
       (QualIdent.unqualify import_name)
       (Loc.start_line decl_loc))

(** Warns if the import [import_name] of a single member, with [targets], is hidden by a
    declaration in the current scope, or else records it in case one follows. An import of
    the declared symbol itself is merely redundant. *)
let check_named_import ~diagnostics ~import_loc ~import_name ~targets tbl =
  let name = QualIdent.unqualify import_name in
  let declared =
    match Hashtbl.find (get_scope_entries tbl.tbl_curr) name with
    | Some (Symbol qi | Alias { target = qi; _ } | Transparent qi) -> [ qi ]
    | Some (Functions { imported = false; targets }) -> targets
    | Some (Import _ | Functions { imported = true; _ }) | None -> []
  in
  match declared with
  | [] ->
      set_in_scope tbl
        (get_scope_named_imports tbl.tbl_curr)
        ~key:name
        ~data:(import_loc, import_name, targets)
  | decl :: _ ->
      if not (denote_same targets declared tbl) then
        warn_hidden_import ~diagnostics ~import_loc ~import_name
          ~decl_loc:(QualIdent.to_loc decl)

(** Warns if a recorded import of a single member named [name] into [scope] is hidden by
    the declaration [symbol_qual_ident] at [decl_loc]. *)
let check_hidden_by_declaration ~diagnostics scope name symbol_qual_ident decl_loc tbl =
  let named_imports = get_scope_named_imports scope in
  Option.iter (Hashtbl.find named_imports name)
    ~f:(fun (import_loc, import_name, targets) ->
      remove_from_scope tbl named_imports name;
      if not (denote_same targets [ symbol_qual_ident ] tbl) then
        warn_hidden_import ~diagnostics ~import_loc ~import_name ~decl_loc)

let import_binding ~loc ~name ~target ~symbol tbl =
  let function_ = is_function symbol in
  let entries = get_scope_entries tbl.tbl_curr in
  let set_entry entry =
    invalidate_caches tbl;
    set_in_scope tbl entries ~key:name ~data:entry
  in
  match Hashtbl.find entries name with
  | None ->
      let entry =
        if function_ then Functions { imported = true; targets = [ target ] }
        else Import target
      in
      set_entry entry
  | Some (Functions { imported = true; targets }) when function_ ->
      let already_imported =
        List.exists targets ~f:(fun existing -> QualIdent.equal existing target)
        || begin
          let target_identity = identity target tbl in
          List.exists targets ~f:(fun existing ->
              QualIdent.equal (identity existing tbl) target_identity)
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
let import ~diagnostics import_instr (tbl : t) : t =
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
            when Module.is_named_functor mdef.mod_decl ->
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
  if not (import_instr.import_all || import_instr.import_prelude) then
    check_named_import ~diagnostics ~import_loc ~import_name:unresolved
      ~targets:(List.map imported ~f:(fun (_, target, _, _) -> target))
      tbl;
  List.iter imported ~f:(fun (_, imported_ident, symbol, _) ->
      match (symbol, import_instr.import_all) with
      | ModDef mdef, true ->
          (* Generic members are retained for later implicit instantiation. *)
          let is_generic = Module.is_named_functor mdef.mod_decl in
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
      add_to_map tbl entries (Ident.to_loc ident) ident (Transparent target)
        ~duplicate:(fun map key data -> set_in_scope tbl map ~key ~data)
  end;
  tbl

(** Add [symbol] to the appropriate scope of [tbl]. Fails if [symbol] already exists in
    this scope. Appropriate scope is equal to the current scope in most cases. Except if
    [symbol] is something other than a local variable definition and current scope is a
    callable scope (determined by scope.scope_is_local), then the parent scope is used
    instead. *)
let add_symbol ?(scope : scope option = None) ~diagnostics symbol tbl =
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
      | Import _ | Functions { imported = true; _ } ->
          check_hidden_by_declaration ~diagnostics appropriate_scope key symbol_qual_ident
            symbol_loc tbl;
          set_in_scope tbl map ~key ~data
      | _ -> Error.redeclaration_error symbol_loc (Ident.to_string key)
    in

    match symbol with
    | CallDef call when is_function symbol ->
        let source = Callable.source_ident call in
        let entries = get_scope_entries appropriate_scope in
        let targets =
          match Hashtbl.find entries source with
          | None -> []
          | Some (Import _) | Some (Functions { imported = true; _ }) ->
              check_hidden_by_declaration ~diagnostics appropriate_scope source
                symbol_qual_ident symbol_loc tbl;
              []
          | Some (Functions { imported = false; targets }) -> targets
          | Some _ -> Error.redeclaration_error symbol_loc (Ident.to_string source)
        in
        if Map.mem tbl.tbl_symbols symbol_qual_ident then
          Error.redeclaration_error symbol_loc (Ident.to_string source);
        if not (Ident.equal source symbol_ident) then
          add_to_map tbl entries symbol_loc symbol_ident (Symbol symbol_qual_ident)
            ~duplicate;
        set_in_scope tbl entries ~key:source
          ~data:(Functions { imported = false; targets = symbol_qual_ident :: targets });
        let symbol_scope = create_scope symbol_qual_ident false true in
        add_to_map tbl
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
        add_to_map tbl
          (get_scope_entries appropriate_scope)
          symbol_loc symbol_ident (Transparent target_qual_ident) ~duplicate;
        tbl
    | ModInst mod_inst ->
        let transparent_alias =
          match mod_inst.mod_inst_def with
          | Some (Module.Alias target) when not mod_inst.mod_inst_is_sealed ->
              let _, public, symbol, _ = resolve_and_find_exn target tbl in
              begin match symbol with
              | Module.ModDef
                  {
                    mod_decl =
                      { mod_decl_is_sealed = true; mod_decl_parameters = Structure; _ };
                    _;
                  } ->
                  None
              | _ -> Some public
              end
          | None | Some _ -> None
        in
        begin match transparent_alias with
        | Some target ->
            add_to_map tbl
              (get_scope_entries appropriate_scope)
              symbol_loc symbol_ident (Transparent target) ~duplicate;
            tbl
        | None ->
            let mod_inst_qual_ident, subst, sealed, permits_members =
              match mod_inst.mod_inst_def with
              | Some application -> (
                  let mod_inst_func = Module.application_target application in
                  let mod_inst_args = Module.application_args application in
                  let declaration, mod_inst_func, mod_inst_symbol, subst1 =
                    resolve_and_find_exn mod_inst_func tbl
                  in
                  let own_instance =
                    match mod_inst_symbol with
                    | Module.ModDef m ->
                        module_is_instantiated declaration m.mod_decl subst1
                    | _ -> is_instance subst1
                  in
                  let permits_members =
                    match (application, mod_inst_symbol) with
                    | Module.Alias _, Module.ModDef m ->
                        own_instance || Module.is_structure m.mod_decl
                    | Module.Alias _, _ -> false
                    | Module.Apply _, _
                    | Module.CanonicalApply _, _
                    | Module.ApplyUnit _, _ ->
                        true
                  in
                  let formals =
                    match mod_inst_symbol with
                    | Module.ModDef mdef ->
                        begin match application with
                        | Module.Alias _ -> []
                        | Apply _ | CanonicalApply _ | ApplyUnit _ ->
                            if not own_instance then Module.formals mdef.mod_decl else []
                        end
                    | _ ->
                        Error.type_error
                          (QualIdent.to_loc mod_inst_func)
                          "Expected module identifier"
                  in
                  let res =
                    List.map2 formals mod_inst_args ~f:(fun formal arg ->
                        let formal_id =
                          QualIdent.append mod_inst_func formal.mod_inst_name
                        in
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
                  let res =
                    match res with
                    | Unequal_lengths -> List.Or_unequal_lengths.Unequal_lengths
                    | Ok subst ->
                        Ok
                          (match application with
                          | Module.ApplyUnit _ ->
                              ( Module.unit_parameter_path mod_inst_func,
                                QualIdent.to_list
                                  (Module.unit_parameter_path symbol_qual_ident) )
                              :: subst
                          | Alias _ | Apply _ | CanonicalApply _ -> subst)
                  in
                  let shared =
                    List.map mod_inst.mod_inst_shared ~f:(fun (generated, inst) ->
                        (generated, QualIdent.to_list inst))
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
                                {
                                  mod_decl_is_sealed = true;
                                  mod_decl_returns = [ iface ];
                                  _;
                                };
                              _;
                            } ->
                            Some iface
                        | Module.ModDef { mod_decl = { mod_decl_returns; _ }; _ }
                          when mod_inst.mod_inst_is_sealed ->
                            let _, named, _, _ =
                              resolve_and_find_exn mod_inst.mod_inst_type tbl
                            in
                            let found =
                              if QualIdent.equal declaration named then
                                let arguments =
                                  match mod_inst_symbol with
                                  | Module.ModDef m ->
                                      List.map (Module.formals m.mod_decl)
                                        ~f:(fun formal ->
                                          Module.ModArg
                                            (QualIdent.requalify (qid_subst subst1)
                                               (QualIdent.append declaration
                                                  formal.mod_inst_name)))
                                  | _ -> []
                                in
                                Some (named, arguments)
                              else
                                List.find mod_decl_returns ~f:(fun (iface_ident, _) ->
                                    let _, iface_ident, _, _ =
                                      resolve_and_find_exn iface_ident tbl
                                    in
                                    QualIdent.equal iface_ident named)
                            in
                            if Option.is_none found then
                              Error.type_error mod_inst.mod_inst_loc
                                (Printf.sprintf
                                   !"Module %{QualIdent} does not declare that it \
                                     implements interface %{QualIdent}, so %{Ident} \
                                     cannot be sealed with it"
                                   mod_inst_func mod_inst.mod_inst_type
                                   mod_inst.mod_inst_name);
                            found
                        | _ -> None
                      in
                      match sealed_iface with
                      | Some (iface_ident, iface_args)
                        when permits_members
                             && ((not own_instance) || mod_inst.mod_inst_is_sealed)
                             && not inside_functor ->
                          (* Outside a sealed functor, an instance is a view of its
                         interface, applied to the functor's interface arguments. *)
                          let requalify = QualIdent.requalify (qid_subst subst1) in
                          let iface_ident = requalify iface_ident in
                          let iface_args =
                            List.map iface_args ~f:(function
                              | Module.ModArg qi -> Module.ModArg (requalify qi)
                              | Module.TypeArg _ as arg -> arg)
                          in
                          let _, iface_ident, iface_symbol, _ =
                            resolve_and_find_exn iface_ident tbl
                          in
                          let iface_formals =
                            match iface_symbol with
                            | Module.ModDef idef -> Module.formals idef.mod_decl
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
                          let iface_subst =
                            match (application, iface_symbol) with
                            | ( (Module.ApplyUnit _ | Alias _),
                                Module.ModDef
                                  {
                                    mod_decl = { mod_decl_parameters = UnitParameter; _ };
                                    _;
                                  } )
                              when own_instance
                                   ||
                                   match application with
                                   | ApplyUnit _ -> true
                                   | _ -> false ->
                                ( Module.unit_parameter_path iface_ident,
                                  QualIdent.to_list
                                    (Module.unit_parameter_path symbol_qual_ident) )
                                :: iface_subst
                            | _ -> iface_subst
                          in
                          let sealed_args =
                            List.filter_map subst ~f:(fun (formal_id, arg_path) ->
                                if Module.is_unit_parameter_path formal_id then None
                                else
                                  Some
                                    ( QualIdent.unqualify formal_id,
                                      QualIdent.from_list arg_path ))
                          in
                          let sealed_functor, sealed_args =
                            Option.value
                              (application_origin mod_inst_func tbl)
                              ~default:(mod_inst_func, sealed_args)
                          in
                          let unit_markers =
                            List.filter
                              (subst @ qid_subst subst1)
                              ~f:(fun (source, _) -> Module.is_unit_parameter_path source)
                          in
                          let inherited_shared =
                            match application with
                            | Module.Alias _ ->
                                List.filter (qid_subst subst1) ~f:(fun (source, _) ->
                                    match Map.find tbl.tbl_symbols source with
                                    | Some
                                        (Module.ModInst
                                           { mod_inst_def = Some (CanonicalApply _); _ })
                                      ->
                                        true
                                    | _ -> false)
                            | _ -> []
                          in
                          let iface_subst =
                            List.fold (unit_markers @ inherited_shared) ~init:iface_subst
                              ~f:(fun mappings ((source, _) as binding) ->
                                if List.Assoc.mem mappings source ~equal:QualIdent.equal
                                then mappings
                                else mappings @ [ binding ])
                          in
                          ( iface_ident,
                            iface_subst @ shared,
                            Some
                              {
                                sealed_functor;
                                sealed_interface = iface_ident;
                                sealed_args;
                              },
                            permits_members )
                      | _ -> (mod_inst_func, subst @ shared, None, permits_members))
                  | Unequal_lengths ->
                      Error.type_error
                        (QualIdent.to_loc mod_inst_func)
                        (Printf.sprintf
                           !"Module %{QualIdent} expects %d arguments"
                           mod_inst_func (List.length formals)))
              | None ->
                  let declaration, mod_inst_type, mod_inst_symbol, subst =
                    resolve_and_find_exn mod_inst.mod_inst_type tbl
                  in
                  let permits_members =
                    match mod_inst_symbol with
                    | Module.ModDef m ->
                        Module.is_structure m.mod_decl
                        || module_is_instantiated declaration m.mod_decl subst
                    | _ -> false
                  in
                  (mod_inst_type, [], None, permits_members)
            in
            let is_abstract = mod_inst.mod_inst_is_interface in
            add_to_map tbl
              (get_scope_entries appropriate_scope)
              symbol_loc symbol_ident
              (Alias
                 {
                   is_abstract;
                   is_alias =
                     (match mod_inst.mod_inst_def with
                     | Some (Module.Alias _) -> true
                     | _ -> false);
                   permits_members;
                   target = mod_inst_qual_ident;
                   substitution = subst;
                 })
              ~duplicate;
            begin match sealed with
            | Some data ->
                {
                  tbl with
                  tbl_sealed = Map.set tbl.tbl_sealed ~key:symbol_qual_ident ~data;
                }
            | None -> tbl
            end
        end
    | _ -> (
        add_to_map tbl
          (get_scope_entries appropriate_scope)
          symbol_loc symbol_ident (Symbol symbol_qual_ident) ~duplicate;
        let new_map = Map.add_exn tbl.tbl_symbols ~key:symbol_qual_ident ~data:symbol in
        let tbl = { tbl with tbl_symbols = new_map } in
        match symbol with
        | ModDef mod_def ->
            let is_abstract =
              mod_def.mod_decl.mod_decl_is_interface || Module.is_functor mod_def.mod_decl
            in
            let symbol_scope = create_scope symbol_qual_ident is_abstract false in
            add_to_map tbl
              (get_scope_children appropriate_scope)
              symbol_loc symbol_ident symbol_scope;
            tbl
        | CallDef _ ->
            let symbol_scope = create_scope symbol_qual_ident false true in
            add_to_map tbl
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
let add_local_vars ~diagnostics var_decls tbl =
  let curr_scope = tbl.tbl_curr in
  List.fold_left var_decls ~init:tbl ~f:(fun tbl var_decl ->
      let var_ident = var_decl.Type.var_name in
      let curr_entries = get_scope_entries curr_scope in
      let var_def = Module.VarDef { var_decl; var_init = None; var_is_free = NotFree } in
      match Hashtbl.find curr_entries var_ident with
      | None -> add_symbol ~diagnostics var_def tbl
      | Some (Symbol qual_ident) ->
          let tbl_symbols = Map.set tbl.tbl_symbols ~key:qual_ident ~data:var_def in
          { tbl with tbl_symbols }
      | _ -> tbl (* a local variable can't be an alias *))
