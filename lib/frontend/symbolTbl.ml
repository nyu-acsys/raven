(** Symbol table data structure *)

open Base
open Ast
open Util

let unknown_ident_error loc id =
  Error.error loc ("Unknown identifier " ^ QualIdent.to_string id ^ ".")

type data_type_constr = {
  constr_name : Ident.t;
  constr_return_type : type_expr;
  constr_args : var_decl list;
}

type data_type_destr = {
  destr_name : Ident.t;
  destr_arg : type_expr;
  destr_return_type : type_expr;
}

type typing_env =
  | TypeAlias of Module.type_alias
  | Callable of Callable.call_decl
  | ModAlias of Module.module_alias
  | ModDecl of (Module.t * Module.t) 
  (* the first component stores the processed module and the second component is to store the original un-processed module definition. This is used to instantiate module aliases. *)
  | RAModDecl of (Module.t * Module.t)
  | VarDecl of var_decl
  | Field of Module.field_def
  | DataTypeConstr of data_type_constr
  | DataTypeDestr of data_type_destr
        
let typing_env_to_string t =
  match t with
  | TypeAlias tp -> "TypeAlias(" ^ Ident.to_string tp.type_alias_name ^ " --> " ^ (match tp.type_alias_def with | None -> "None" | Some tp -> (Type.to_string tp)) ^ ")"
  | Callable call_decl ->
    Printf.sprintf "CallDecl(%s())" (Ident.to_string call_decl.call_decl_name)
  | ModAlias mod_alias ->
    "ModAlias(" ^ Ident.to_string mod_alias.mod_alias_name ^ ")"
  | ModDecl (m, _orig_mod) ->
    "ModDecl(" ^ Ident.to_string m.module_decl.mod_decl_name ^ ")"
  | RAModDecl (m, _orig_mod) ->
    "ResourceAlgebraModuleDecl(" ^ Ident.to_string m.module_decl.mod_decl_name ^ ")" 
  | VarDecl var_decl -> "VarDecl(" ^ Ident.to_string var_decl.var_name ^ ": " ^ Type.to_string var_decl.var_type ^ ")"
  | Field field_decl ->
    "Field("
    ^ Ident.to_string field_decl.field_name
    ^ " : "
    ^ Type.to_string field_decl.field_type
    ^ ")"
  | DataTypeConstr data_type_constr ->
    Printf.sprintf "DataTypeConstr(%s (%s) : %s)" (Ident.to_string data_type_constr.constr_name) (Print.string_of_format Type.pr_var_decl_list data_type_constr.constr_args) (Type.to_string data_type_constr.constr_return_type)
  | DataTypeDestr data_type_destr ->
    Printf.sprintf "DataTypeDestr(%s (%s) : %s)" (Ident.to_string data_type_destr.destr_name) (Type.to_string data_type_destr.destr_arg) (Type.to_string data_type_destr.destr_return_type)


type type_qual_ident_map = typing_env qual_ident_map

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


let fully_qualified loc (iden : qual_ident) tbl =
  let rec fully_qualified_helper (iden : qual_ident) tbl =
    match tbl with
    | [] -> iden
    | (label, _) :: ts -> (
        match label with
        | None -> iden
        | Some iden' -> fully_qualified_helper (QualIdent.left_append iden' iden) ts)

  in
  let rec fully_qualified iden tbl =
  match tbl with
    | [] -> unknown_ident_error loc iden
    | (label, map) :: ts -> (
        match Map.find map iden with 
        | None -> fully_qualified iden ts
        | Some _ -> fully_qualified_helper iden ((label, map) :: ts))
  in
  fully_qualified iden tbl


let add (tbl : t) name tp : t =
  let rec add_helper tbl name tp_mem =
    match tbl with
    | [] -> []
    | t :: ts ->
      let label, map = t in
      let t' =
        match Map.find map name with
        | None -> (label, Map.add_exn map ~key:name ~data:tp_mem)
        | Some _ ->
          Logs.debug (fun m -> m "%s" @@ "Overriding " ^ QualIdent.to_string name);
          let map = Map.set map ~key:name ~data:tp_mem in
          (label, map)
          
      (* Map.remove map name in *)
      (* (label, Map.add_exn map' ~key:name ~data:tp_mem) *)
      in

      let ts' =
        match label with
        | None -> ts
        | Some iden ->
          add_helper ts (QualIdent.left_append iden name) tp_mem
      in
      
      t' :: ts'
  in

  Logs.debug
    (fun m -> m "ADDING %s -> %s\n%s"
        (QualIdent.to_string name) (typing_env_to_string tp) (to_string tbl));
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

let find_exn loc (tbl : t) name =
  match find tbl name with
  | Some decl -> decl
  | None -> unknown_ident_error loc name

let equal (_tp_env1: t) (_tp_env2: t) : bool =
  true (* TODO: Implement properly *)
