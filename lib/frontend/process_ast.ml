open Base
open Ast
open Util

module SymbolTbl = struct
  type typing_env =
    | TypeExpr of type_expr
    | Callable of Callable.call_decl
    | ModAlias of Module.module_alias
    | ModDecl of Module.module_decl
    | VarDecl of var_decl
    | Field of Module.field_def

  let typing_env_to_string t =
    match t with
    | TypeExpr tp -> "TypeExpr(" ^ Type.to_string tp ^ ")"
    | Callable call_decl ->
        "CallDecl(" ^ Ident.to_string call_decl.call_decl_name ^ ")"
    | ModAlias mod_alias ->
        "ModAlias(" ^ Ident.to_string mod_alias.mod_alias_name ^ ")"
    | ModDecl mod_decl ->
        "ModDecl(" ^ Ident.to_string mod_decl.mod_decl_name ^ ")"
    | VarDecl var_decl -> "VarDecl(" ^ Ident.to_string var_decl.var_name ^ ")"
    | Field field_decl ->
        "Field("
        ^ Ident.to_string field_decl.field_name
        ^ " : "
        ^ Type.to_string field_decl.field_type
        ^ ")"

  type type_qual_ident_map = typing_env qual_ident_map

  (* type t = (ident ident_map) list *)

  type t = (ident option * type_qual_ident_map) list

  let label_to_string label =
    match label with None -> "__" | Some iden -> Ident.to_string iden

  let rec to_string tbl =
    let rec list_to_string t =
      match t with
      | [] -> " "
      | (k, v) :: ms ->
          (QualIdent.to_string k ^ " -> " ^ typing_env_to_string v ^ "\n")
          ^ list_to_string ms
    in

    match tbl with
    | [] -> "end\n\n"
    | t :: ts ->
        label_to_string (fst t)
        ^ " :: [ "
        ^ list_to_string (Map.to_alist (snd t))
        ^ " ]\n" ^ to_string ts

  let push ?(name = None) tbl : t = (name, Map.empty (module QualIdent)) :: tbl
  let push_name name tbl = push ~name:(Some name) tbl

  let pop tbl =
    match tbl with [] -> raise (Failure "Empty symbol table") | _ :: ts -> ts

  (*
  let rec fully_qualified (id: qual_ident) tbl = match tbl with
    | [] -> id
    | (label, _) :: ts -> match label with
        | None -> id
        | Some iden -> fully_qualified (QualIdent.left_append iden id) ts

 *)

  let add (tbl : t) name tp =
    let rec add_helper tbl name tp_mem =
      match tbl with
      | [] -> []
      | t :: ts ->
          let label, map = t in
          let t' =
            match Map.find map name with
            | None -> (label, Map.add_exn map ~key:name ~data:tp_mem)
            | Some _ ->
                print_debug ("Overriding " ^ QualIdent.to_string name);
                let map' = Map.remove map name in
                (label, Map.add_exn map' ~key:name ~data:tp_mem)
          in

          let ts' =
            match label with
            | None -> ts
            | Some iden ->
                add_helper ts (QualIdent.left_append iden name) tp_mem
          in

          t' :: ts'
    in

    print_debug
      ("ADDING " ^ QualIdent.to_string name ^ " -> " ^ typing_env_to_string tp
     ^ "\n" ^ to_string tbl);
    match tbl with
    | [] -> raise (Failure "Empty symbol table")
    | tbl -> add_helper tbl name tp

  (* let remove tbl name = print_debug ("Removing " ^ QualIdent.to_string name ^ "\n" ^ to_string tbl);
     match tbl with
       | [] -> raise(Failure "Empty symbol table")
       | t :: ts -> let (label, map) = t in
           (label, (Map.remove map name)) :: ts
  *)
  (* let declared_in_current tbl name =
     Map.mem (fst (List.hd tbl)) name
  *)

  let find_local tbl name =
    match tbl with [] -> None | (_, map) :: _ -> Map.find name map

  let rec find (tbl : t) name =
    match tbl with
    | [] -> None
    | (_, map) :: ts -> (
        match Map.find map name with None -> find ts name | Some id -> Some id)
end

let rec pre_process_module (m: Module.t0) : (Module.t1) = 

  let rec extract_members (mod_decl: Module.module_decl) (sorted_members: Module.sorted_member_def_list) (mod_defs_list: Module.member_def list) : (Module.module_decl * Module.sorted_member_def_list) =

    match mod_defs_list with
    | [] -> (mod_decl, sorted_members)
    | def :: defs -> (
      match def with
      | TypeAlias type_alias ->
        let mod_decl = { mod_decl with 
          mod_decl_rep = if type_alias.type_alias_rep then
              Some type_alias.type_alias_name
              else mod_decl.mod_decl_rep;
          mod_decl_types = Map.add_exn mod_decl.mod_decl_types ~key: type_alias.type_alias_name ~data: type_alias;
        } in

        let sorted_members = { sorted_members with
          types' = type_alias :: sorted_members.types';
        } in

        extract_members mod_decl sorted_members defs

      | Import import_dir ->
        let sorted_members = { sorted_members with
          imports' = import_dir :: sorted_members.imports';
        } in
        
        extract_members mod_decl sorted_members defs

      | ModDef module_def -> (
        match module_def with
        | ModImpl mod_impl ->
          let mod_decl = { mod_decl with
            mod_decl_mod_defs = Map.add_exn mod_decl.mod_decl_mod_defs ~key:mod_impl.mod_decl.mod_decl_name ~data:mod_impl.mod_decl;
          } in

          let sorted_members = { sorted_members with
            mod_defs' = (pre_process_module mod_impl) :: sorted_members.mod_defs';
          } in

          extract_members mod_decl sorted_members defs

        | ModAlias mod_alias ->
          let mod_decl = { mod_decl with
            mod_decl_mod_aliases = Map.add_exn mod_decl.mod_decl_mod_aliases ~key:mod_alias.mod_alias_name ~data:mod_alias;
          } in

          let sorted_members = { sorted_members with
            mod_aliases' = mod_alias :: sorted_members.mod_aliases';
          } in

          extract_members mod_decl sorted_members defs
      )

      | FieldDef field_def ->
        let mod_decl = { mod_decl with
          mod_decl_fields = Map.add_exn mod_decl.mod_decl_fields ~key: field_def.field_name ~data: field_def.field_type
        } in

        let sorted_members = { sorted_members with
          fields' = field_def :: sorted_members.fields';
        } in
        
        extract_members mod_decl sorted_members defs

      | ValDef v ->
          let mod_decl = { mod_decl with
            mod_decl_vars = Map.add_exn mod_decl.mod_decl_vars ~key:v.var_decl.var_name ~data:v.var_decl;
          } in

          let sorted_members = { sorted_members with
            vars' = v :: sorted_members.vars';
          } in

          extract_members mod_decl sorted_members defs

      | CallDef call ->
        let cl_decl =
          match call with
          | FuncDef fn -> fn.func_decl
          | ProcDef proc -> proc.proc_decl
        in

        let mod_decl = { mod_decl with
          mod_decl_callables = Map.add_exn mod_decl.mod_decl_callables ~key:cl_decl.call_decl_name ~data:cl_decl;
        } in

        let sorted_members = { sorted_members with
          call_defs' = call :: sorted_members.call_defs';
        } in

        extract_members mod_decl sorted_members defs
    )

  in

  let mod_decl, sorted_mems = extract_members m.mod_decl Module.empty_sorted_member_def_list m.mod_def  in
  {
    module_decl' = mod_decl;
    members' = sorted_mems;
    interface' = m.mod_interface;
  }



let process_module (m: Module.t1) (tbl: SymbolTbl.t) : Module.t =
  let rec resolve_imports (import_directives: Module.import_directive list) (mod_decl: Module.module_decl) (tbl: SymbolTbl.t) : Module.module_decl =
     
    let merging_function _ v = match v with
    | `Left v1 -> Some v1
    | `Right v2 -> Some v2
    | `Both (v1, `v2) -> Some v1

    in

    match import_directives with
    | [] -> mod_decl
    | imp :: import_directives' -> 

      let imported_mod_decl = Module.empty_decl in


      let mod_decl = { mod_decl with
        mod_decl_rep = mod_decl.mod_decl_rep;
        mod_decl_fields = Map.merge_skewed mod_decl.mod_decl_fields imported_mod_decl.mod_decl_fields ~combine:merging_function;
        mod_decl_mod_defs = mod_decl.mod_decl_mod_defs;
        mod_decl_mod_aliases = mod_decl.mod_decl_mod_aliases;
        mod_decl_types = mod_decl.mod_decl_types;
        mod_decl_callables = mod_decl.mod_decl_callables;
        mod_decl_vars = mod_decl.mod_decl_vars;
      } in

      resolve_imports import_directives' mod_decl tbl