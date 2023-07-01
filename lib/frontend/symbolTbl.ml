(** Symbol table data structure *)

open Base
open Ast
open Util

let unknown_ident_error loc id =
  Error.error loc ("Unknown identifier " ^ QualIdent.to_string id ^ ".")

type entry =
  | Symbol of QualIdent.t
  | Alias of QualIdent.t * QualIdent.subst

type scope =
  { (* Fully qualified identifier of this scope *)
    scope_id: QualIdent.t;
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
      | Module.TypeDef tp -> "TypeDef(" ^ Ident.to_string tp.type_def_name ^ " --> " ^ (match tp.type_def_expr with | None -> "None" | Some tp -> (Type.to_string tp)) ^ ")"
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
        Printf.sprintf "DataTypeConstr(%s (%s) : %s)" (Ident.to_string data_type_constr.constr_name) (Print.string_of_format Type.pr_var_decl_list data_type_constr.constr_args) (Type.to_string data_type_constr.constr_return_type)
      | DestrDef data_type_destr ->
        Printf.sprintf "DataTypeDestr(%s (%s) : %s)" (Ident.to_string data_type_destr.destr_name) (Type.to_string data_type_destr.destr_arg) (Type.to_string data_type_destr.destr_return_type)
  (*  end
  | Alias id ->
    Printf.sprintf !"Alias(%{QualIdent})" id*)
  
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

let create_scope qual_ident = 
  { scope_id = qual_ident;
    scope_entries = Hashtbl.create (module Ident);
    scope_children = Hashtbl.create (module Ident);
    scope_cache = Hashtbl.create (module QualIdent);
  }

let create () =
  let root_id = QualIdent.from_ident (Ident.make "$Root" 0) in
  let root_scope = create_scope root_id in
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
    
(** Resolve [name] to its fully qualified identifier relative to the current scope in [tbl]. *)
let resolve name (tbl : t) : (QualIdent.t * QualIdent.t * QualIdent.subst) option =
  let open Option.Syntax in
  let rec go_forward scope subst ids =
    match ids with
    | [] -> Some (get_scope_id scope, subst)
    | first_id :: ids1 ->
      let scope_symbols = get_scope_entries scope in
      let* entry = Hashtbl.find scope_symbols first_id in
      match entry, ids1 with
      | Alias (qual_ident, subst1), _ ->
        let subst = subst1 @ (qual_ident, fully_qualify first_id scope tbl) :: subst in
        go_forward tbl.tbl_root subst (QualIdent.to_list qual_ident @ ids1)
      | Symbol qual_ident, [] -> Some (qual_ident, subst)
      | _ ->
        let scope_children = get_scope_children scope in
        let* cscope = Hashtbl.find scope_children first_id in
        go_forward cscope subst ids1
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
            let+ alias_qual_ident, subst = go_forward curr_scope [] (QualIdent.to_list name) in
            let orig_qual_ident =
              (if QualIdent.(get_scope_id curr_scope = root_ident tbl)
               then name
               else QualIdent.concat (get_scope_id curr_scope) name) |>
              QualIdent.requalify subst
            in
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
  Logs.debug (fun m -> m "%a" QualIdent.pr orig_qual_ident);
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

let add_to_map map loc key data =
  match Hashtbl.add map ~key ~data with
  | `Ok -> ()
  | `Duplicate -> Error.redeclaration_error loc (Ident.to_string key)

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
          let symbol_name = Module.symbol_to_name symbol in
          let symbol_ident = QualIdent.append unresolved_imported_ident symbol_name in
          let _, symbol_fully_qual_ident, _, _ = resolve_and_find_exn import_loc symbol_ident tbl in
          add_to_map (get_scope_entries curr_scope) import_loc symbol_name (Alias (symbol_fully_qual_ident, []))
        | _ -> ())
  | _ ->
    let alias_ident = QualIdent.unqualify unresolved_imported_ident in
    add_to_map (get_scope_entries curr_scope) import_loc alias_ident (Alias (imported_ident, []))
  in
  tbl
  
(** Add [symbol] to the current scope of [tbl]. Fails if [symbol] already exists in this scope. *)
let add_symbol symbol tbl =
  let rec add symbol tbl =
    let curr_scope = tbl.tbl_curr in
    let symbol_ident = Module.symbol_to_name symbol in
    let symbol_loc = Module.symbol_to_loc symbol in
    let symbol_qual_ident = fully_qualify symbol_ident tbl.tbl_curr tbl in
    match symbol with
    | ModInst mod_inst ->
      let mod_inst_qual_ident, subst =
        match mod_inst.mod_inst_def with
        | None ->
          let _, mod_inst_type, _mod_inst_symbol, _ = resolve_and_find_exn mod_inst.mod_inst_loc mod_inst.mod_inst_type tbl in
          mod_inst_type, []
        | Some (_mod_inst_func, _mod_inst_args) ->
          failwith "not yet implemented"
      in
      add_to_map (get_scope_entries curr_scope) symbol_loc symbol_ident (Alias (mod_inst_qual_ident, subst));
      tbl
    | _ ->
      add_to_map (get_scope_entries curr_scope) symbol_loc symbol_ident (Symbol symbol_qual_ident);
      let new_map = Map.add_exn tbl.tbl_symbols ~key:symbol_qual_ident ~data:symbol in
      let tbl = { tbl with tbl_symbols = new_map } in
      match symbol with
      | ModDef _mod_def ->
        let symbol_scope = create_scope symbol_qual_ident in
        add_to_map (get_scope_children curr_scope) symbol_loc symbol_ident symbol_scope;
        (*let tbl = enter symbol_loc symbol_ident tbl in
          let mod_def_formals =
          List.map mod_def.mod_decl.mod_decl_formals
          ~f: (fun mod_def_formal -> Module.SymbolDef (ModInst mod_def_formal))
          in
          let tbl = List.fold_left (mod_def_formals @ mod_def.mod_def) ~init:tbl
          ~f:(fun tbl -> function
              | SymbolDef symbol -> add symbol tbl
              | Import import_instr -> import import_instr tbl)
          in
          exit tbl*)
          tbl
      | CallDef _ -> 
        let symbol_scope = create_scope symbol_qual_ident in
        add_to_map (get_scope_children curr_scope) symbol_loc symbol_ident symbol_scope;
        tbl
      | _ -> tbl
  in
  add symbol tbl

(** Update [symbol] in the current scope of [tbl]. Assumes that [symbol] is already present in this scope. *)
let set_symbol symbol tbl : t =
  let symbol_ident = Module.symbol_to_name symbol in
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
  
