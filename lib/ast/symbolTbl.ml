(** Symbol table data structure *)

open Base
open AstDef
open Util

let unknown_ident_error loc id =
  Error.error loc ("Unknown identifier " ^ QualIdent.to_string id ^ ".")

type entry =
  | Symbol of QualIdent.t
  | Alias of bool * QualIdent.t * QualIdent.subst
  | Import of QualIdent.t

type scope =
  { (* Fully qualified identifier of this scope *)
    scope_id: QualIdent.t;
    (* Indicates whether this scope is an uninstantiated module functor or interface *)
    scope_is_abstract: bool;
    (* Scopes of submodules / callables *)
    scope_children: scope IdentHashtbl.t; [@hash.ignore]
    (* Symbols defined in this scope *)
    scope_entries: entry IdentHashtbl.t; [@hash.ignore]
    (* Cache that maps names (partially) qualified names to fully qualified names, relative to this scope. *)
    scope_cache: (QualIdent.t * QualIdent.t * QualIdent.subst) QualIdentHashtbl.t; [@hash.ignore]
  } [@@deriving hash]

let get_scope_entries { scope_entries; _ } = scope_entries

let get_scope_children { scope_children; _ } = scope_children

let get_scope_cache { scope_cache; _ } = scope_cache

let get_scope_id { scope_id; _ } = scope_id

(*let is_local = function
  | Local _ -> true
  | _ -> false*)

type t = {
  (* Root scope *)
  tbl_root: scope;
  (* Current scope *)
  tbl_curr: scope;
  (* Stack of remaining open scopes *)
  tbl_path: scope list;
  (* Mapping from fully qualified names to the symbols that they represent *)
  tbl_symbols: Module.symbol QualIdentMap.t;
}

let entry_to_string = function
  (*| Symbol symbol ->
    begin match symbol with*)
  | Module.TypeDef tp ->
    "TypeDef(" ^ Ident.to_string tp.type_def_name ^ " --> " ^ (match tp.type_def_expr with | None -> "None" | Some tp -> (Type.to_string tp)) ^ ")"
      | CallDef call_def ->
        Printf.sprintf "CallDef(%s())" (Ident.to_string (Callable.to_ident call_def))
      | ModInst mod_inst ->
        "ModInst(" ^ Ident.to_string mod_inst.mod_inst_name ^ ")"
      | ModDef m ->
        "ModDef(" ^ Ident.to_string m.mod_decl.mod_decl_name ^ ")"
      | VarDef var_def -> "VarDecl(" ^ Ident.to_string var_def.var_decl.var_name ^ ": " ^ Type.to_string var_def.var_decl.var_type ^ ")"
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
      (QualIdent.to_string k ^ " -> " ^ entry_to_string v ^ "\n")
      ^ list_to_string ms
  in

  match tbl with
  | [] -> "end\n\n"
  | t :: ts ->
    label_to_string (fst t)
    ^ " :: [ "
    ^ list_to_string (Map.to_alist (snd t))
    ^ " ]\n" ^ to_string ts

let create_scope qual_ident is_abstract = 
  { scope_id = qual_ident;
    scope_is_abstract = is_abstract;
    scope_entries = Hashtbl.create (module Ident);
    scope_children = Hashtbl.create (module Ident);
    scope_cache = Hashtbl.create (module QualIdent);
  }

let create () =
  let root_id = QualIdent.from_ident (Ident.make "$Root" 0) in
  let root_scope = create_scope root_id false in
  { tbl_root = root_scope;
    tbl_curr = root_scope;
    tbl_path = [];
    tbl_symbols = Map.empty (module QualIdent);
  }

(** Reset table to the root scope *)
let reset tbl =
  { tbl with
    tbl_curr = tbl.tbl_root;
    tbl_path = [] }

(** Return the name of the root scope of [tbl] *)
let root_ident tbl = tbl.tbl_root.scope_id

(** Check whether current scope of [tbl] is the root scope *)
let curr_is_root tbl = List.is_empty tbl.tbl_path

(** Fully qualify [ident] relative to [scope] in [tbl]. *)
let fully_qualify ident scope tbl : QualIdent.t =
  let scope_ident = get_scope_id scope in
  if QualIdent.(scope_ident = root_ident tbl)
  then QualIdent.from_ident ident 
  else QualIdent.append scope_ident ident

let pr_subst ppf subst =
  let open Stdlib.Format in
  fprintf ppf "[ @[%a@] ]" (Print.pr_list_sep ",\n" (fun ppf (a, b) -> fprintf ppf "%a -> %a" QualIdent.pr a QualIdent.pr (QualIdent.from_list b))) subst


(** Check whether [scope] is a parent of the current scope in [tbl]. *)
let is_parent scope tbl =
  let scope_id = get_scope_id scope in
  List.exists (tbl.tbl_curr :: tbl.tbl_path) ~f:(fun p -> QualIdent.(get_scope_id p = scope_id))


(** Resolve [name] to its fully qualified identifier relative to the current scope in [tbl]. *)
let resolve name (tbl : t) : (QualIdent.t * QualIdent.t * QualIdent.subst) option =
  let open Option.Syntax in
  let rec go_forward inst_scopes scope subst ids =
    match ids with
    | [] -> Some (get_scope_id scope, subst)
    | first_id :: ids1 ->
      if scope.scope_is_abstract &&
         not @@ is_parent scope tbl &&
         not @@ Set.mem inst_scopes (get_scope_id scope)
      then None
      else begin
      let scope_symbols = get_scope_entries scope in
      let* entry = Hashtbl.find scope_symbols first_id in
      match entry, ids1 with
      | Alias (is_abstract, qual_ident, subst1), _ ->
        let subst1 = List.map subst1 ~f:(fun (s, t) -> QualIdent.requalify subst s, t) in
        let target_qual_ident = QualIdent.requalify subst qual_ident in
        let new_path = QualIdent.requalify_path subst1 (QualIdent.to_list target_qual_ident @ ids1) in
        let subst =
          subst1 @ 
          (target_qual_ident, fully_qualify first_id scope tbl |> QualIdent.to_list) :: subst
        in
        let new_inst_scopes =
          if is_abstract then inst_scopes else Set.add inst_scopes target_qual_ident
        in
        go_forward new_inst_scopes tbl.tbl_root subst new_path
      | Import qual_ident, _ ->
        let target_qual_ident = QualIdent.requalify subst qual_ident in
        let new_path = QualIdent.to_list target_qual_ident @ ids1 in
        if is_parent scope tbl
        then go_forward inst_scopes tbl.tbl_root subst new_path
        else None
      | Symbol qual_ident, [] -> Some (qual_ident, subst)
      | _ ->
        let scope_children = get_scope_children scope in
        let* cscope = Hashtbl.find scope_children first_id in
        go_forward inst_scopes cscope subst ids1
    end
  in
  let first_id = QualIdent.first_ident name in 
  let rec go_backward is_first curr_scope path =
    let scope_cache = get_scope_cache curr_scope in
    (if is_first then
       Hashtbl.find scope_cache name
     else None) |> Option.or_else () ~f:(fun _ ->
        let+ alias_qual_ident, orig_qual_ident, subst =
          if Hashtbl.mem (get_scope_entries curr_scope) first_id
          then
            let+ alias_qual_ident, subst = go_forward (Set.empty (module QualIdent)) curr_scope [] (QualIdent.to_list name) in
            let orig_qual_ident = alias_qual_ident |> QualIdent.requalify subst in
            alias_qual_ident, orig_qual_ident, subst
          else
            let* curr_scope1, path1 =
              match path with
              | s :: ss -> Some (s, ss)
              | [] -> None
            in
            go_backward false curr_scope1 path1
        in
          if is_first then Hashtbl.add_exn scope_cache ~key:name ~data:(alias_qual_ident, orig_qual_ident, subst);
          alias_qual_ident, orig_qual_ident, subst
        )
  in
  go_backward true tbl.tbl_curr tbl.tbl_path

(** Like [resolve] but throws an exception if [name] is not found in [tbl]. *)
let resolve_exn loc name tbl =
  resolve name tbl |>
  Option.lazy_value ~default:(fun () -> unknown_ident_error loc name)
      
(** Resolve [name] relative to the current scope in [tbl] and return:
    - the fully qualified name of the associated symbol, relative to the scope where the symbol is declared
    - the fully qualified name of the associated symbol, relative to the scope where the symbol is used
    - the associated symbol, relative to the scope where the symbol is declared
    - a substitution map that maps the symbol definition to the scope where it is used.
*)
let resolve_and_find name tbl : (QualIdent.t * QualIdent.t * Module.symbol * QualIdent.subst) option =
  let open Option.Syntax in
  let* alias_qual_ident, orig_qual_ident, subst = resolve name tbl in
  Logs.debug (fun m -> m "SymbolTbl.resolve_and_find %a = " QualIdent.pr name);
  Logs.debug (fun m -> m "orig_qual_ident: %a" QualIdent.pr orig_qual_ident);
  Logs.debug (fun m -> m "alias_qual_ident: %a" QualIdent.pr alias_qual_ident);
  Logs.debug (fun m -> m "subst: %a\n" pr_subst subst);
  let+ symbol = Map.find tbl.tbl_symbols alias_qual_ident in
  alias_qual_ident, orig_qual_ident, symbol, subst

(** Like [resolve_and_find] but throws an exception if [name] is not found in [tbl]. *)
let resolve_and_find_exn loc name (tbl : t) =
  resolve_and_find name tbl |>
  Option.lazy_value ~default:(fun () -> unknown_ident_error loc name)

(** Find the symbol associated with [name] relative to the current scope in [tbl]. *)
let find name tbl : (Module.symbol * QualIdent.subst) option =
  let open Option.Syntax in
  let* alias_qual_ident, _, subst = resolve name tbl in
  let+ symbol = Map.find tbl.tbl_symbols alias_qual_ident in
  symbol, subst

(** Like [find] but throws an exception if [name] is not found in [tbl]. *)
let find_exn loc name (tbl : t) =
  find name tbl |>
  Option.lazy_value ~default:(fun () -> unknown_ident_error loc name)

(** Enter the scope [name] from the current scope in [tbl]. *)
let enter loc name tbl : t =
  let open Option.Syntax in
  (let scope_children = get_scope_children tbl.tbl_curr in
   let+ scope = Hashtbl.find scope_children name in
   { tbl with tbl_curr = scope; tbl_path = tbl.tbl_curr :: tbl.tbl_path }) |>
  Option.lazy_value ~default:(fun () -> Error.internal_error loc (Printf.sprintf !"Did not find subscope %{Ident} in scope %{QualIdent}" name (get_scope_id tbl.tbl_curr)))

(** Exit the current scope in [tbl]. *)
let exit tbl : t =
  match tbl.tbl_path with
  | scope :: path -> { tbl with tbl_curr = scope; tbl_path = path }
  | [] -> failwith "Empty symbol table"


(** Go to the scope in [tbl] that declares the symbol associated with absolute identifier [name] *)
let goto loc name tbl : t =
  List.fold_left (QualIdent.path name) ~init:(reset tbl) ~f:(fun tbl ident -> enter loc ident tbl)

let add_to_map map loc key ?(duplicate = fun _ _ _ -> Error.redeclaration_error loc (Ident.to_string key)) data =
  match Hashtbl.add map ~key ~data with
  | `Ok -> ()
  | `Duplicate -> duplicate map key data
    

(** Add an alias based on the import instruction [import_instr] *)
let rec import import_instr (tbl : t) : t =
  let open Module in
  let import_loc = import_instr.import_loc in
  let unresolved_imported_ident = import_instr.import_name in
  let _, imported_ident, symbol, _ = resolve_and_find_exn import_loc unresolved_imported_ident tbl in
  let curr_scope = tbl.tbl_curr in
  let _ = match symbol with
    | ModDef { mod_def ; _ } ->
      List.iter mod_def ~f:(function
        | SymbolDef symbol ->
          let symbol_name = Symbol.to_name symbol in
          let symbol_ident = QualIdent.append unresolved_imported_ident symbol_name in
          let _, symbol_fully_qual_ident, _, _ = resolve_and_find_exn import_loc symbol_ident tbl in
          add_to_map (get_scope_entries curr_scope) import_loc symbol_name (Import symbol_fully_qual_ident)
            ~duplicate:(fun _ _ _ -> ())
        | _ -> ())
  | _ ->
    let alias_ident = QualIdent.unqualify unresolved_imported_ident in
    add_to_map (get_scope_entries curr_scope) import_loc alias_ident (Import imported_ident)
      ~duplicate:(fun _ _ _ -> ())
  in
  tbl
  
(** Add [symbol] to the current scope of [tbl]. Fails if [symbol] already exists in this scope. *)
let add_symbol symbol tbl =
  let rec add symbol tbl =
    let curr_scope = tbl.tbl_curr in
    let symbol_ident = Symbol.to_name symbol in
    let symbol_loc = Symbol.to_loc symbol in
    let symbol_qual_ident = fully_qualify symbol_ident tbl.tbl_curr tbl in
    let duplicate (map: entry IdentHashtbl.t) (key : Ident.t) data =
      match Hashtbl.find_exn map key with
      | Import _ -> Hashtbl.set map ~key ~data
      | _ -> Error.redeclaration_error symbol_loc (Ident.to_string key)
    in
    match symbol with
    | ModInst mod_inst ->
      let mod_inst_qual_ident, subst =
        match mod_inst.mod_inst_def with
        | None ->
          let _, mod_inst_type, _mod_inst_symbol, _ = resolve_and_find_exn mod_inst.mod_inst_loc mod_inst.mod_inst_type tbl in
          mod_inst_type, []
        | Some (mod_inst_func, mod_inst_args) ->
          let _, mod_inst_func, mod_inst_symbol, _subst1 = resolve_and_find_exn mod_inst.mod_inst_loc mod_inst_func tbl in
          let formals = match mod_inst_symbol with
            | Module.ModDef mdef ->
              mdef.mod_decl.mod_decl_formals
            | _ -> Error.type_error symbol_loc "Expected module identifier"
          in
          let res = List.map2 formals mod_inst_args ~f:(fun formal arg ->
              let formal_id = QualIdent.append mod_inst_func formal.mod_inst_name in
              let _, arg, _arg_symbol, _arg_subst = resolve_and_find_exn mod_inst.mod_inst_loc arg tbl in
              (formal_id, QualIdent.to_list arg)
            )
          in
          match res with
          | Ok subst -> mod_inst_func, subst
          | Unequal_lengths ->
            Error.type_error symbol_loc
              (Printf.sprintf !"Module %{QualIdent} expects %d arguments" mod_inst_func (List.length formals))
      in
      let is_abstract = mod_inst.mod_inst_is_interface in
      add_to_map (get_scope_entries curr_scope) symbol_loc symbol_ident (Alias (is_abstract, mod_inst_qual_ident, subst))
        ~duplicate;
      tbl
    | _ ->
      add_to_map (get_scope_entries curr_scope) symbol_loc symbol_ident (Symbol symbol_qual_ident) ~duplicate;
      let new_map = Map.add_exn tbl.tbl_symbols ~key:symbol_qual_ident ~data:symbol in
      let tbl = { tbl with tbl_symbols = new_map } in
      match symbol with
      | ModDef mod_def ->
        let is_abstract = mod_def.mod_decl.mod_decl_is_interface || List.length mod_def.mod_decl.mod_decl_formals > 0 in
        let symbol_scope = create_scope symbol_qual_ident is_abstract in
        add_to_map (get_scope_children curr_scope) symbol_loc symbol_ident symbol_scope;
        tbl
      | CallDef _ -> 
        let symbol_scope = create_scope symbol_qual_ident false in
        add_to_map (get_scope_children curr_scope) symbol_loc symbol_ident symbol_scope;
        tbl
      | _ -> tbl
  in
  add symbol tbl

(** Update [symbol] in the current scope of [tbl]. Assumes that [symbol] is already present in this scope. *)
let set_symbol symbol tbl : t =
  let symbol_ident = Symbol.to_name symbol in
  let symbol_qual_ident = fully_qualify symbol_ident tbl.tbl_curr tbl in
  let new_map = Map.set tbl.tbl_symbols ~key:symbol_qual_ident ~data:symbol in
  { tbl with tbl_symbols = new_map }
 

(** Add local variable declarations [var_decls] to the current scope in [tbl].
    Updates the symbol definition if a variable is already present. *)
let add_local_vars var_decls tbl = 
  let curr_scope = tbl.tbl_curr in
  List.fold_left var_decls ~init:tbl ~f:(fun tbl var_decl ->
      let var_ident = var_decl.Type.var_name in
      let curr_entries = get_scope_entries curr_scope in
      let var_def = Module.VarDef { var_decl = var_decl; var_init = None } in
      match Hashtbl.find curr_entries var_ident with
      | None -> add_symbol var_def tbl
      | Some Symbol qual_ident ->
        let tbl_symbols = Map.set tbl.tbl_symbols ~key:qual_ident ~data:var_def in
        { tbl with tbl_symbols }
      | _ -> tbl (* a local variable can't be an alias *)
    )
  
