open Base
open Ast
open Util
open Error

(* Generic_Error is thrown by functions which don't have any Loc information. These exceptions are then meant to be caught by a caller function which can then generate the appropriate Error.errors with appropriate Loc information attached  *)
  
module SymbolTbl = struct
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


 let rec fully_qualified (iden : qual_ident) tbl =
  let rec fully_qualified_helper (iden : qual_ident) tbl =
    match tbl with
    | [] -> iden
    | (label, _) :: ts -> (
        match label with
        | None -> iden
        | Some iden' -> fully_qualified_helper (QualIdent.left_append iden' iden) ts)

  in

  match tbl with
    | [] -> raise (Generic_Error ("Ident " ^ QualIdent.to_string iden ^ " not found in typing env"))
    | (label, map) :: ts -> (
        match Map.find map iden with 
        | None -> fully_qualified iden ts
        | Some _ -> fully_qualified_helper iden ((label, map) :: ts))



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
                print_debug ("Overriding " ^ QualIdent.to_string name);
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

  let equal (_tp_env1: t) (_tp_env2: t) : bool =
    true (* TODO: Implement properly *)
end

let type_mismatch_error loc exp_ty fnd_ty =
  let ty_str ty = "expression of type\n  " ^ Type.to_string ty ^ "\n" in
  Error.type_error loc
    ("Expected an " ^ ty_str exp_ty ^ "but found an " ^ ty_str fnd_ty)

let arguments_to_string d =
  if d = 1 then "one argument" else Printf.sprintf "%d arguments" d
    
let module_arg_mismatch_error loc typ_constr expected =
  Error.type_error loc (Printf.sprintf "Module %s expects %s." (Type.to_name typ_constr) (arguments_to_string expected))

let unknown_ident_error id loc =
  Error.error loc ("Unknown identifier " ^ QualIdent.to_string id ^ ".")
    
    
let rec pre_process_module (m: Module.t0) : (Module.t) = 

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
          types = type_alias :: sorted_members.types;
        } in

        extract_members mod_decl sorted_members defs

      | Import import_dir ->
        let sorted_members = { sorted_members with
          imports = import_dir :: sorted_members.imports;
        } in
        
        extract_members mod_decl sorted_members defs

      | ModDef module_def -> (
        match module_def with
        | ModImpl mod_impl ->
          let mod_decl = { mod_decl with
            mod_decl_mod_defs = Map.add_exn mod_decl.mod_decl_mod_defs ~key:mod_impl.mod_decl.mod_decl_name ~data:mod_impl.mod_decl;
          } in

          let sorted_members = { sorted_members with
            mod_defs = (pre_process_module mod_impl) :: sorted_members.mod_defs;
          } in

          extract_members mod_decl sorted_members defs

        | ModAlias mod_alias ->
          let mod_decl = { mod_decl with
            mod_decl_mod_aliases = Map.add_exn mod_decl.mod_decl_mod_aliases ~key:mod_alias.mod_alias_name ~data:mod_alias;
          } in

          let sorted_members = { sorted_members with
            mod_aliases = mod_alias :: sorted_members.mod_aliases;
          } in

          extract_members mod_decl sorted_members defs
      )

      | FieldDef field_def ->
        let mod_decl = { mod_decl with
          mod_decl_fields = Map.add_exn mod_decl.mod_decl_fields ~key: field_def.field_name ~data: field_def
        } in

        let sorted_members = { sorted_members with
          fields = field_def :: sorted_members.fields;
        } in
        
        extract_members mod_decl sorted_members defs

      | ValDef v ->
          let mod_decl = { mod_decl with
            mod_decl_vars = Map.add_exn mod_decl.mod_decl_vars ~key:v.var_decl.var_name ~data:v.var_decl;
          } in

          let sorted_members = { sorted_members with
            vars = v :: sorted_members.vars;
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
          call_defs = call :: sorted_members.call_defs;
        } in

        extract_members mod_decl sorted_members defs
    )

  in

  (* let mod_aliases = List.map (Map.to_alist m.mod_decl.mod_decl_mod_aliases) ~f:snd in *)


  let mod_decl, sorted_mems = extract_members m.mod_decl Module.empty_sorted_member_def_list (List.rev m.mod_def)  in

  (* let sorted_mems = { sorted_mems with
    mod_aliases = mod_aliases @ sorted_mems.mod_aliases;
    (* This is taking all formal arguments to module which are stored in module_decl and adding them as mod_aliases to the members of the module. 
      This is required because formal arguments are added to the module_decl by parser, but not to body of module. *)
  } in *)
  {
    module_decl = mod_decl;
    members = sorted_mems;
    interface = m.mod_interface;
    obligations = Module.empty_sorted_member_def_list;
  }

module ProcessTypeExpr = struct
  let rec process_type_expr (tp_expr: type_expr) (tbl: SymbolTbl.t) : type_expr = 
    let open Type in
    match tp_expr with
    | App ((Var qual_ident), tp_list, tp_attr) ->
      (match tp_list with
      | [] -> (
        let fully_qualified_qual_ident = SymbolTbl.fully_qualified qual_ident tbl in
        (match SymbolTbl.find tbl fully_qualified_qual_ident with
        | Some (TypeAlias _tp_alias) -> App ((Var fully_qualified_qual_ident), [], tp_attr)
        | Some (ModDecl (m, _orig_mod)) | Some RAModDecl (m, _orig_mod) -> (
          match m.module_decl.mod_decl_rep with
          | None -> Error.type_error tp_attr.type_loc ("Expected Type Expr" ^ Type.to_string tp_expr ^ "; found Module in typing environment without a Rep Type")
          | Some iden -> 
            let new_fully_qualified_qual_ident = QualIdent.append fully_qualified_qual_ident iden in
            (match SymbolTbl.find tbl new_fully_qualified_qual_ident with
            | Some (TypeAlias _tp_alias) -> App ((Var new_fully_qualified_qual_ident), [], tp_attr)
            | _ -> Error.type_error tp_attr.type_loc ("Internal Error: Expected Type Expr" ^ Type.to_string tp_expr ^ "; rep type in Module not actually a TpExpr")
            )
        )
        (* | Some (RAModDecl _) -> App (Var fully_qualified_qual_ident, [], tp_attr) *)
        | Some (ModAlias _mod_alias) -> Error.unsupported_error tp_attr.type_loc @@ Printf.sprintf "Module Aliases typing not supported\n %s" (SymbolTbl.to_string tbl)
        | _ -> Error.type_error tp_attr.type_loc ("Module cannot be instantiated in this context.")
        )

        
      )
      | _ -> Error.type_error tp_attr.type_loc ("Module " ^ QualIdent.to_string qual_ident ^ " cannot be instantiated in this context.")
      (* TODO *)
      )

    | App (Set, tp_list, tp_attr) ->
      (match tp_list with
      | [tp_arg] -> let tp_arg' = process_type_expr tp_arg tbl in
        App (Set, [tp_arg'], tp_attr)
      | _ -> module_arg_mismatch_error (Type.to_loc tp_expr) Set 1
      )

    | App (Map, tp_list, tp_attr) ->
      (match tp_list with
      | [tp1; tp2] -> let tp1 = process_type_expr tp1 tbl in
        let tp2 = process_type_expr tp2 tbl in
        App (Map, [tp1; tp2], tp_attr)
      | _ -> module_arg_mismatch_error (Type.to_loc tp_expr) Map 2
      )

    | App (Data _variant_decl_list, _tp_list, _tp_attr) ->
      (* (match tp_list with
      | [] -> 

        (* constr_map is constructed just to make sure no duplicate constructors are used in data type declaration. *)
        let constr_map = List.fold variant_decl_list ~init:(Map.empty (module Ident))  ~f:(fun mp variant_decl -> 
          List.fold variant_decl.variant_args ~init:mp ~f:(fun mp var_arg ->
            match
              (Map.add mp ~key:var_arg.var_name ~data:var_arg)
            with
            | `Ok mp -> mp
            | `Duplicate -> Error.error (Type.to_loc tp_expr) @@ Printf.sprintf "Duplicate constructor found in data type %s" (Type.to_string tp_expr)
            )
        ) in

        
        let variant_decl_list = List.map variant_decl_list ~f:(fun variant_decl -> 
          let args = List.map variant_decl.variant_args ~f:(fun var_decl -> process_var_decl var_decl tbl) in

          { variant_decl with
            variant_args = args
          }
        ) in 

        let tbl = List.fold variant_decl_list ~init:tbl ~f:(fun tbl variant_decl -> 
          let tbl = List.fold variant_decl.variant_args ~init:tbl ~f:(fun tbl var_arg ->
            let data_type_destr = {
              destr_name = var_arg.var_name;
              destr_arg = ;
              destr_return_type = var_arg.var_type;
            }
            SymbolTbl.add tbl (QualIdent.from_ident var_arg.var_name) (DataTypeDestr )
          ) in  
          
        ) in
          
          
          
        ()

      | _ -> raise (Generic_Error "Data types don't take arguments")
      ) *)
      raise (Generic_Error "Data Types can only be defined as new types. Not used indirectly.")

    | App (constr, [], tp_attr) -> App (constr, [], tp_attr)

    | App (constr, _tp_list, _tp_attr) -> raise (Generic_Error (Type.to_name constr ^ " types don't take arguments"))


  and expand_type_expr (tp_expr: type_expr) (tbl: SymbolTbl.t) : type_expr = 
    match tp_expr with
    | App (constr, tp_expr_list, tp_attr) ->

      let expanded_tp_expr_list = List.map tp_expr_list ~f:(fun tp_expr -> expand_type_expr tp_expr tbl) in

      match constr with
      | Var qual_iden ->
        (* Var types with args not supported. Polymorphic types need to be instantiated as separate modules before using. *)
        (
        (match SymbolTbl.find tbl qual_iden with
        | Some (TypeAlias tp_alias) ->
          (match tp_alias.type_alias_def with
          | None -> tp_expr
          | Some tp_expr -> expand_type_expr tp_expr tbl)
        
        | Some _ -> Error.error (Type.to_loc tp_expr) "Expected type_alias in env here."
        | None -> Error.error (Type.to_loc tp_expr) "Expected type_alias in env here."
        ))

      | _ -> App(constr, expanded_tp_expr_list, tp_attr)
    


  and process_var_decl (var_decl: var_decl) (tbl: SymbolTbl.t) : var_decl = 
    if (not (Type.equal var_decl.var_type (Type.any)))
      then
        { var_decl with
          var_type = process_type_expr var_decl.var_type tbl;
        }
    else
      Error.error (var_decl.var_loc) @@ Printf.sprintf "Type annotation missing for variable '%s'" (Ident.to_string var_decl.var_name)

end

let does_expr_implement_type (expr: expr) (tp_expr: type_expr) (tbl: SymbolTbl.t): unit = 
  let tp1 = ProcessTypeExpr.expand_type_expr (Expr.attr_of expr).expr_type tbl in
  let tp2 = ProcessTypeExpr.expand_type_expr tp_expr tbl in
  (* TODO: Generalize appropriately *)
  if Type.compare (Type.meet tp1 tp2) tp2 <> 0 then
    type_mismatch_error (Expr.loc expr) tp2 tp1

let rec process_expr (expr: expr) (tbl: SymbolTbl.t) : expr = 
  match expr with
  | App (constr, expr_list, expr_attr) ->
    (* let expr_list = List.map expr_list ~f:(fun expr -> process_expr expr tbl) in *)
    let expr_type = expr_attr.expr_type in

    (* The parser returns expressions with expr_type Any. That is why Type.meet is used in the below definitions. It works with the Any type annotations received from the parser, as well as with more precise type annotations. *)

    (* This function is called directly on expressions AST received from parser. That is why, this method must be called on each sub-expression recursively before using them.
    
    This function will also type-check each expression and populate the expr.expr_attr.expr_type with the appropriate type.
    *)

    (match constr, expr_list with
    | Null, [] -> 
      let tp = Type.meet expr_type Type.ref in
      if Type.compare tp Type.ref = 0 then
        let expr_attr = { expr_attr with
          expr_type = Type.ref;
        } in

        App (constr, [], expr_attr)
      else
        Error.lexical_error (Expr.loc expr) ( (Expr.constr_to_string constr ^ " should have a Ref type instead of " ^ Type.to_string expr_type ^ " or " ^ Type.to_string tp))
    | Null, _expr_list -> Error.lexical_error (Expr.loc expr) ((Expr.constr_to_string constr ^ " takes no arguments"))
    
    | Unit, [] -> 
      if Type.equal (Type.meet expr_type (Type.unit)) ((Type.unit)) then
        let expr_attr = { expr_attr with
          expr_type = (Type.unit);
        } in

        App (constr, [], expr_attr)
      else
        Error.lexical_error (Expr.loc expr) ((Expr.constr_to_string constr ^ " should have type Unit instead of " ^ Type.to_string expr_type))
    | Unit, _expr_list -> Error.lexical_error (Expr.loc expr) ((Expr.constr_to_string constr ^ " takes no arguments"))
    
    | Empty, [] ->
      let tp = (Type.meet expr_type (Type.set_typed Type.any)) in
      (match tp with
      | Type.App (Set, _, _) -> 
        let expr_attr = { expr_attr with
          expr_type = tp;
        } in

        App (constr, [], expr_attr)

      | _ -> Error.type_error (Expr.loc expr) ((Expr.constr_to_string constr ^ " should have a Set type instead of " ^ Type.to_string expr_type ^ " or " ^ Type.to_string tp))
        )
    | Empty, _expr_list -> Error.lexical_error (Expr.loc expr) ((Expr.constr_to_string constr ^ " takes no arguments"))

    | Bool _b, [] -> 
      let tp = Type.meet expr_type Type.bool in
      if Type.compare tp Type.bool = 0 then
        let expr_attr = { expr_attr with
          expr_type = Type.bool;
        } in

        App (constr, [], expr_attr)
      else
        Error.type_error (Expr.loc expr) ((Expr.constr_to_string constr ^ " should have a Bool type instead of " ^ Type.to_string expr_type ^ " or " ^ Type.to_string tp))
    | Bool _b, _expr_list -> Error.lexical_error (Expr.loc expr) ((Expr.constr_to_string constr ^ " takes no arguments"))
      
    | Int _num, [] ->
      let tp = Type.meet expr_type Type.int in
      if Type.compare tp Type.int = 0 then
        let expr_attr = { expr_attr with
          expr_type = Type.int;  
        } in

        App (constr, [], expr_attr)
      else
        Error.type_error (Expr.loc expr) ((Expr.constr_to_string constr ^ " should have a Int type instead of " ^ Type.to_string expr_type ^ " or " ^ Type.to_string tp))
    | Int _num, _expr_list -> Error.lexical_error (Expr.loc expr) ((Expr.constr_to_string constr ^ " takes no arguments"))

    | Real _num, [] ->
      let tp = Type.meet expr_type Type.real in 
      if Type.equal tp Type.real then
        let expr_attr = { expr_attr with
        expr_type = Type.real;
        } in

        App (constr, [], expr_attr)
      else
        Error.type_error (Expr.loc expr) ((Expr.constr_to_string constr ^ " should have a Real type instead of " ^ Type.to_string expr_type ^ " or " ^ Type.to_string tp))

    | Real _num, _ -> Error.lexical_error (Expr.loc expr) ((Expr.constr_to_string constr ^ " takes no arguments"))

    | Not, [expr_arg] ->
      let expr_arg = process_expr expr_arg tbl in
      let tp = Type.meet expr_type (Expr.to_type expr_arg) in
      if Type.compare tp Type.bool = 0 then
        let expr_attr = { expr_attr with
          expr_type = Type.bool;  
        } in

        App (constr, [expr_arg], expr_attr)
      else
        Error.type_error (Expr.loc expr) ((Expr.to_string expr_arg ^ " should have a Bool type instead of " ^ Type.to_string (Expr.to_type expr_arg)))

    | Not, _expr_list -> Error.lexical_error (Expr.loc expr) ((Expr.constr_to_string constr ^ " takes exactly one argument"))
    
    | Uminus, [expr_arg] ->
      let expr_arg = process_expr expr_arg tbl in
      let tp = Type.meet expr_type (Expr.to_type expr_arg) in
      if Type.is_num tp then
        let expr_attr = { expr_attr with
          expr_type = tp;  
        } in

        App (constr, [expr_arg], expr_attr)
      else
        Error.lexical_error (Expr.loc expr) ((Expr.to_string expr_arg ^ " should have Int type instead of " ^ Type.to_string (Expr.to_type expr_arg)))
    | Uminus, _expr_list -> Error.lexical_error (Expr.loc expr) ((Expr.constr_to_string constr ^ " takes exactly one argument"))

    | MapLookUp, [expr1; expr2] ->
      let expr1 = process_expr expr1 tbl in
      let tp1 = (Expr.to_type expr1) in

      let expr2 = process_expr expr2 tbl in
      let tp2 = (Expr.to_type expr2) in

      (match tp1 with
      | App (Map, tp_list, _tp_attr) -> (
        (match tp_list with
        | [tp_index; tp_val] -> (
          if (Type.compare tp_index tp2 = 0) then 
            let tp = Type.meet expr_type tp_val in
            if (Type.compare tp tp_val = 0) then
              let expr_attr = { expr_attr with
                expr_type = tp;
              } in

              App (MapLookUp, [expr1; expr2], expr_attr)
            
            else
              Error.type_error (Expr.loc expr) ((Expr.to_string expr ^ " should have type " ^ Type.to_string tp_val ^ "; found: " ^ Type.to_string expr_type))
          else
            Error.type_error (Expr.loc expr) (("Index type mismatch for Map expr " ^ Expr.to_string expr1 ^ ". Expected " ^ Type.to_string tp_index ^ "; found " ^ Type.to_string tp2))
        )
        | _ -> Error.type_error (Expr.loc expr1) ((Expr.to_string expr1 ^ " has Map type but it should have 2 arguments. Instead of " ^ Type.to_string tp1))

        )
      )
      | _ -> Error.type_error (Expr.loc expr1) ((Expr.to_string expr1 ^ " should have Map type instead of " ^ Type.to_string tp1))
      )
    
    | MapLookUp, _expr_list -> Error.lexical_error (Expr.loc expr) ((Expr.constr_to_string constr ^ " takes exactly two arguments"))

    | Eq, [expr1; expr2] ->
      let expr1 = process_expr expr1 tbl in
      let expr2 = process_expr expr2 tbl in

      let tp = Type.meet (Expr.to_type expr1) (Expr.to_type expr2) in
      if not (Type.is_any tp) then
        let expr_attr = { expr_attr with
          expr_type = Type.bool;
        } in

        App (constr, [Expr.set_type expr1 tp; Expr.set_type expr2 tp], expr_attr)
        (* TODO: Check this type-casting is sound. *)
      else
        Error.lexical_error (Expr.loc expr) ((Expr.constr_to_string constr ^ " args should have same type, instead of " ^ Type.to_string (Expr.to_type expr1) ^ " and " ^ Type.to_string (Expr.to_type expr2))) 
    | Eq, _expr_list -> Error.lexical_error (Expr.loc expr) ((Expr.constr_to_string constr ^ " takes exactly two arguments"))

    | Gt, [expr1; expr2] | Lt, [expr1; expr2] | Geq, [expr1; expr2] | Leq, [expr1; expr2] ->
      let expr1 = process_expr expr1 tbl in
      let expr2 = process_expr expr2 tbl in

      let tp1 = ProcessTypeExpr.expand_type_expr (Expr.to_type expr1) tbl in
      let tp2 = ProcessTypeExpr.expand_type_expr (Expr.to_type expr2) tbl in

      let tp = Type.join tp1 tp2 in
      if Type.is_num tp then
        let expr_attr = { expr_attr with
          expr_type = Type.bool;
        } in

        App (constr, [expr1; expr2], expr_attr)
      else
        Error.lexical_error (Expr.loc expr) (Printf.sprintf "%s args should be of Int type, instead of %s and %s; %s" (Expr.constr_to_string constr) (Type.to_string tp1)  (Type.to_string tp2) (Type.to_string tp)) 
    | Gt, _expr_list | Lt, _expr_list | Geq, _expr_list | Leq, _expr_list -> Error.lexical_error (Expr.loc expr) ((Expr.constr_to_string constr ^ " takes exactly two arguments"))

    | Diff, [expr1; expr2] | Union, [expr1; expr2] | Inter, [expr1; expr2] ->
      let expr1 = process_expr expr1 tbl in
      let expr2 = process_expr expr2 tbl in

      let tp = Type.join (Expr.to_type expr1) (Expr.to_type expr2) in
      if Type.is_set tp then
        let expr_attr = { expr_attr with
          expr_type = tp;
        } in

        App (constr, [expr1; expr2], expr_attr)
      else
        Error.lexical_error (Expr.loc expr) ((Expr.constr_to_string constr ^ " args should be of Set type, instead of " ^ Type.to_string (Expr.to_type expr1) ^ " and " ^ Type.to_string (Expr.to_type expr2))) 
    | Diff, _expr_list | Union, _expr_list | Inter, _expr_list -> Error.lexical_error (Expr.loc expr) ((Expr.constr_to_string constr ^ " takes exactly two arguments"))
    
    | Subseteq, [expr1; expr2] ->
      let expr1 = process_expr expr1 tbl in
      let expr2 = process_expr expr2 tbl in

      let tp = Type.join (Expr.to_type expr1) (Expr.to_type expr2) in
      if Type.is_set tp then
        let expr_attr = { expr_attr with
          expr_type = Type.bool;
        } in

        App (Subseteq, [expr1; expr2], expr_attr)
      else
        Error.lexical_error (Expr.loc expr) ((Expr.constr_to_string constr ^ " args should be of Set type, instead of " ^ Type.to_string (Expr.to_type expr1) ^ " and " ^ Type.to_string (Expr.to_type expr2))) 

    | Subseteq, _expr_list -> Error.lexical_error (Expr.loc expr) ((Expr.constr_to_string constr ^ " takes exactly two arguments"))

    | Elem, [expr1; expr2] ->
      let expr1 = process_expr expr1 tbl in
      let expr2 = process_expr expr2 tbl in

      if Type.compare (Expr.to_type expr2) (Type.set_typed (Expr.to_type expr1)) = 0 then
        let expr_attr = { expr_attr with
          expr_type = Type.bool
        } in

        App (Elem, [expr1; expr2], expr_attr)
      else
        Error.lexical_error (Expr.loc expr) ((Expr.to_string expr ^ ": first arg and second arg incompatible."))
    | Elem, _expr_list -> Error.lexical_error (Expr.loc expr) ((Expr.constr_to_string constr ^ " takes exactly two arguments"))

    | And, [expr1; expr2] | Or, [expr1; expr2] | Impl, [expr1; expr2] ->
      let expr1 = process_expr expr1 tbl in
      let expr2 = process_expr expr2 tbl in

      let tp = Type.meet (Expr.to_type expr1) (Expr.to_type expr2) in
      if Type.equal tp Type.perm || Type.equal tp Type.bool  then
        let expr_attr = { expr_attr with
          expr_type = tp;
        } in

        App (constr, [expr1; expr2], expr_attr)
      else
        Error.lexical_error (Expr.loc expr) ((Expr.constr_to_string constr ^ " args should be of Bool or Perm type, instead of " ^ Type.to_string (Expr.to_type expr1) ^ " and " ^ Type.to_string (Expr.to_type expr2)))
    | And, _expr_list | Or, _expr_list | Impl, _expr_list -> Error.lexical_error (Expr.loc expr) ((Expr.constr_to_string constr ^ " takes exactly two arguments"))

    | Plus, [expr1; expr2] | Minus, [expr1; expr2] | Mult, [expr1; expr2] | Div, [expr1; expr2] | Mod, [expr1; expr2] ->
      let expr1 = process_expr expr1 tbl in
      let expr2 = process_expr expr2 tbl in

      let tp1 = ProcessTypeExpr.expand_type_expr (Expr.to_type expr1) tbl in
      let tp2 = ProcessTypeExpr.expand_type_expr (Expr.to_type expr2) tbl in

      let tp = Type.join tp1 tp2 in
      if Type.is_num tp 
        (* TODO: Apply expand_type_expr more consistently in codebase. *)
        then
        let expr_attr = { expr_attr with
          expr_type = Expr.to_type expr1;
        } in

        App (constr, [expr1; expr2], expr_attr)
      else
        Error.lexical_error (Expr.loc expr) ((Expr.constr_to_string constr ^ " args should be of Int type, instead of " ^ Type.to_string (Expr.to_type expr1) ^ " and " ^ Type.to_string (Expr.to_type expr2)))
    | Plus, _expr_list | Minus, _expr_list | Mult, _expr_list | Div, _expr_list | Mod, _expr_list -> Error.lexical_error (Expr.loc expr) ((Expr.constr_to_string constr ^ " takes exactly two arguments"))

    | Dot, _expr_list -> Error.lexical_error (Expr.loc expr) ("Dot expressions should not appear in the AST. Unexpected error.")

    | DataConstr, constr_expr :: args_list ->
      let args_list = List.map args_list ~f:(fun expr -> process_expr expr tbl) in

      let constr_qual_ident = 
        try
          SymbolTbl.fully_qualified (ASTUtil.expr_to_qual_ident constr_expr) tbl 
        with Generic_Error msg -> Error.error (Expr.loc expr) msg
      in

      (match SymbolTbl.find tbl constr_qual_ident with
      | Some (DataTypeConstr constr) -> 
        let constr_arg_types_list = List.map constr.constr_args ~f:(fun var_decl -> var_decl.var_type) in

        let args_list =
          match List.map2 args_list constr_arg_types_list
              ~f:(fun expr tp_expr ->
                does_expr_implement_type expr tp_expr tbl;
                Expr.set_type expr tp_expr
                (* TODO: Make sure this 'type-casting' makes sense *))
          with
          | Ok list -> list
          | Unequal_lengths ->
              Error.type_error (Expr.loc expr) (("data constructor " ^ Ident.to_string constr.constr_name ^ " called with incorrect number of arguments" ))
        in

        let tp = constr.constr_return_type in
        let expr_attr =
          { expr_attr with
            expr_type = tp;
          }
        in

        let constr_expr = ASTUtil.qual_ident_to_expr constr_qual_ident (Expr.attr_of constr_expr) in

        App (DataConstr, constr_expr :: args_list, expr_attr)        

      | Some tp_env -> Error.lexical_error (Expr.loc expr) ((QualIdent.to_string constr_qual_ident ^ ": expected to be a DataConstr instead of " ^ SymbolTbl.typing_env_to_string tp_env))
      | None -> Error.lexical_error (Expr.loc expr) ((QualIdent.to_string constr_qual_ident ^ ": not found in TypingEnv"))
      )
      
    | DataConstr, [] -> Error.lexical_error (Expr.loc expr) ((Expr.constr_to_string constr ^ " needs at least one argument (the callable name)"))


    | DataDestr, [expr1; App (Var destr_qual_ident, [], expr_attr')]  -> 
      let expr1 = process_expr expr1 tbl in

      let destr_qual_ident =
        try
          SymbolTbl.fully_qualified destr_qual_ident tbl 
        with Generic_Error msg -> Error.error (Expr.loc expr) msg
      in
      
      (match SymbolTbl.find tbl destr_qual_ident with    
      | Some (DataTypeDestr data_type_destr) ->
        let tp = data_type_destr.destr_return_type in

        let expr_attr' = { expr_attr' with
          expr_type = tp;
        } in

        let (expr2: expr) = App (Var destr_qual_ident, [], expr_attr') in

        if Type.equal (Expr.to_type expr1) (data_type_destr.destr_arg) then
          let expr_attr = { expr_attr with
            expr_type = tp;
          } in

          App (DataDestr, [expr1; expr2], expr_attr)
        
        else
          Error.lexical_error (Expr.loc expr) @@ Printf.sprintf "%s: type mismatch for DataTypeDestr expr. First arg should be of type %s, instead of %s" (Expr.to_string expr) (Type.to_string tp) (Type.to_string (Expr.to_type expr1))
      | Some tp_env -> Error.lexical_error (Expr.loc expr) ((QualIdent.to_string destr_qual_ident ^ ": expected to be a VarDef instead of " ^ SymbolTbl.typing_env_to_string tp_env))
      | None -> Error.lexical_error (Expr.loc expr) ((QualIdent.to_string destr_qual_ident ^ ": not found in TypingEnv"))
      )

    | DataDestr, _ -> Error.lexical_error (Expr.loc expr) ((Expr.constr_to_string constr ^ " takes exactly two arguments"))

    | Call, callable_expr :: args_list ->
      let args_list = List.map args_list ~f:(fun expr -> process_expr expr tbl) in

      let callable_qual_ident = 
        try
          SymbolTbl.fully_qualified (ASTUtil.expr_to_qual_ident callable_expr) tbl 
        with Generic_Error msg -> Error.error (Expr.loc expr) msg
        in
      (match (SymbolTbl.find tbl callable_qual_ident) with
      | Some Callable callable_decl -> 
        let callable_arg_ident_list = callable_decl.call_decl_formals in
        let callable_arg_var_decl_list = List.map callable_arg_ident_list ~f:(fun ident -> match Map.find callable_decl.call_decl_locals ident with | Some var -> var | None -> Error.lexical_error (Expr.loc expr) ("Formal arg variable not found in CallDecl")) in
        let callable_arg_types_list = List.map callable_arg_var_decl_list ~f:(fun var_decl -> var_decl.var_type) in
        let _ =
          match List.map2 args_list callable_arg_types_list ~f:(fun expr tp_expr -> does_expr_implement_type expr tp_expr tbl) with
            (* TODO: Extend for implicit ghost arguments *)
            | Ok _ -> ()
            | Unequal_lengths -> Error.lexical_error (Expr.loc expr) (("Callable " ^ Ident.to_string callable_decl.call_decl_name ^ " called with incorrect number of arguments" ))
        in
        (* TODO: what type to assign to callable expressions which return multiple things? *)
        let tp = 
          match callable_decl.call_decl_kind with
          | Proc | Func ->
              (match callable_decl.call_decl_returns with
              | [] -> Type.unit
              | [ident] -> (match Map.find callable_decl.call_decl_locals ident with
                | Some var_decl -> var_decl.var_type
                | None -> Error.lexical_error (Expr.loc expr) ("Return arg variable not found in CallDecl")
                )
              | _ -> Error.lexical_error (Expr.loc expr) ((Ident.to_string callable_decl.call_decl_name ^ ": Callables which return multiple values not presently supported"))
              )
                
          | Pred | Lemma | Invariant -> Type.perm
        in
        let expr_attr =
          { expr_attr with
            expr_type = tp;
          }
        in

        let callable_expr = ASTUtil.qual_ident_to_expr callable_qual_ident (Expr.attr_of callable_expr) in

        App (Call, callable_expr :: args_list, expr_attr)
        

      | Some (DataTypeConstr _constr) -> process_expr (App (DataConstr, callable_expr :: args_list, Expr.attr_of expr)) tbl

      | Some tp_env -> Error.lexical_error (Expr.loc expr) ((QualIdent.to_string callable_qual_ident ^ ": expected to be a callable instead of " ^ SymbolTbl.typing_env_to_string tp_env))
      | None -> Error.lexical_error (Expr.loc expr) ((QualIdent.to_string callable_qual_ident ^ ": not found in TypingEnv"))
      )
    | Call, [] -> Error.lexical_error (Expr.loc expr) ((Expr.constr_to_string constr ^ " needs at least one argument (the callable name)"))

    | Read, [expr1; App (Var qual_ident, [], expr_attr')] ->
      let expr1 = process_expr expr1 tbl in

      let qual_ident = 
        try
          SymbolTbl.fully_qualified qual_ident tbl 
        with Generic_Error msg -> Error.error (Expr.loc expr) msg
      in
      (match SymbolTbl.find tbl qual_ident with    
      | Some (Field field_def) -> 
        let tp = field_def.field_type in

        let expr_attr' = { expr_attr' with
          expr_type = tp;
        } in

        let (expr2: expr) = App (Var qual_ident, [], expr_attr') in

        if Type.equal (Expr.to_type expr1) (Type.ref) then
            let expr_attr = { expr_attr with
            expr_type = tp;
            } in
  
            App (Read, [expr1; expr2], expr_attr)
  
        else
          Error.lexical_error (Expr.loc expr) ((Expr.to_string expr ^ ": for Read expr, first arg should be a Ref type, instead of " ^ Type.to_string (Expr.to_type expr1)))
      
      | Some (DataTypeDestr data_type_destr) ->
        let tp = data_type_destr.destr_return_type in

        let expr_attr' = { expr_attr' with
          expr_type = tp;
        } in

        let (expr2: expr) = App (Var qual_ident, [], expr_attr') in

        if Type.equal (Expr.to_type expr1) (data_type_destr.destr_arg) then
          let expr_attr = { expr_attr with
            expr_type = tp;
          } in

          App (DataDestr, [expr1; expr2], expr_attr)
        
        else
          Error.lexical_error (Expr.loc expr) @@ Printf.sprintf "%s: type mismatch for DataTypeDestr expr. First arg should be of type %s, instead of %s" (Expr.to_string expr) (Type.to_string tp) (Type.to_string (Expr.to_type expr1))
      | Some tp_env -> Error.lexical_error (Expr.loc expr) ((QualIdent.to_string qual_ident ^ ": expected to be a VarDef instead of " ^ SymbolTbl.typing_env_to_string tp_env))
      | None -> Error.lexical_error (Expr.loc expr) ((QualIdent.to_string qual_ident ^ ": not found in TypingEnv"))
      )

    | Read, _expr_list -> Error.lexical_error (Expr.loc expr) ((Expr.constr_to_string constr ^ " takes exactly two arguments"))

    | Ite, [cond_expr; if_expr; else_expr] ->
      let cond_expr = process_expr cond_expr tbl in
      let if_expr = process_expr if_expr tbl in
      let else_expr = process_expr else_expr tbl in

      if Type.equal (Expr.to_type cond_expr) Type.bool then
        let tp = Type.join (Expr.to_type if_expr) (Expr.to_type else_expr) in
        let expr_attr = { expr_attr with
          expr_type = tp;
        } in

        App (Ite, [cond_expr; if_expr; else_expr], expr_attr)
      else
        Error.lexical_error (Expr.loc expr) ((Expr.to_string cond_expr ^ ": for If-then-else expr, condition expr should be bool, instead of " ^ Type.to_string (Expr.to_type cond_expr)))
    | Ite, _expr_list -> Error.lexical_error (Expr.loc expr) ((Expr.constr_to_string constr ^ " takes exactly three arguments"))

    (* | Write, [expr1; expr2] *)
    | Write, _expr_list -> Error.lexical_error (Expr.loc expr) ("Write expr not presently supported")
    
    | Own, [expr1; expr2; expr3] -> 
      let expr1 = process_expr expr1 tbl in
      let expr2 = process_expr expr2 tbl in
      let expr3 = process_expr expr3 tbl in
      (if (Type.equal Type.ref (Expr.to_type expr1)) then
        (match SymbolTbl.find tbl (ASTUtil.expr_to_qual_ident expr2) with
        | Some (Field field_def) -> (
          (* The following additional call to process_type_expr is required because for fields with custom RAs, their types are stored as module names in typing env. The following call will convert it to appropriate rep type. *)
          let field_type = ProcessTypeExpr.process_type_expr field_def.field_type tbl in

          if (Type.equal (Type.join field_type (Expr.to_type expr3)) field_type) then
            let expr_attr = { expr_attr with
              expr_type = Type.mk_perm (Expr.loc expr);
            } in

            App (Own, [expr1; expr2; expr3], expr_attr)

          else
            Error.type_error (Expr.loc expr) ("Field type mismatch. Field " ^ (Ident.to_string field_def.field_name) ^ " has type " ^ (Type.to_string field_def.field_type ^ "; received " ^ Type.to_string (Expr.to_type expr3))))
        | Some _tp -> Error.type_error (Expr.loc expr) ("Expected Field in typing env. Found" ^ SymbolTbl.typing_env_to_string _tp)
        | None -> Error.type_error (Expr.loc expr) ("Field " ^ (Expr.to_string expr2) ^ "not found in typing env")
        )
        
      else
        Error.type_error (Expr.loc expr) ("Own Predicate used incorrectly; called with args of types: " ^ (Print.string_of_format (Print.pr_list_comma Type.pr) (List.map ~f: (Expr.to_type) [expr1; expr2; expr3])))
      )


    | Own, [expr1; expr2; expr3; expr4] ->
      let expr1 = process_expr expr1 tbl in
      let expr2 = process_expr expr2 tbl in
      let expr3 = process_expr expr3 tbl in
      let expr4 = process_expr expr4 tbl in

      (if (Type.equal Type.ref (Expr.to_type expr1)
      && Type.is_num (Expr.to_type expr4)
        ) then 
          (match SymbolTbl.find tbl (ASTUtil.expr_to_qual_ident expr2) with
          | Some (Field field_def) -> (
            if (Type.equal (Type.join field_def.field_type (Expr.to_type expr3)) field_def.field_type) then
              let expr_attr = {expr_attr with
                expr_type = Type.mk_perm (Expr.loc expr);
              } in

              App (Own, [expr1; expr2; expr3; expr4], expr_attr)
            else 
              Error.type_error (Expr.loc expr) ("Field type mismatch. Field " ^ (Ident.to_string field_def.field_name) ^ " has type " ^ (Type.to_string field_def.field_type ^ "; received " ^ Type.to_string (Expr.to_type expr3))))
          | Some _tp -> Error.type_error (Expr.loc expr) ("Expected Field in typing env. Found" ^ SymbolTbl.typing_env_to_string _tp)
          | None -> Error.type_error (Expr.loc expr) ("Field " ^ (Expr.to_string expr2) ^ "not found in typing env")
          )
      else
          Error.type_error (Expr.loc expr) ("Own Predicate used incorrectly; called with args of types: " ^ (Print.string_of_format (Print.pr_list_comma Type.pr) (List.map ~f: (Expr.to_type) [expr1; expr2; expr3; expr4])))
      ) 

    | Own, _expr_list -> Error.lexical_error (Expr.loc expr) ((Expr.constr_to_string constr ^ " takes either three or four arguments"))
    
    | Setenum, member_expr_list -> 
      let member_expr_list = List.map member_expr_list ~f:(fun expr -> process_expr expr tbl) in
      let member_type_list = (match member_expr_list with 
      | [] -> [Type.any] (* Want empty sets to have type Any instead of Bot*)
      | _ -> List.map member_expr_list ~f:Expr.to_type
      ) in

      let tp = List.fold member_type_list ~init:Type.bot ~f:Type.join in
      let expr_attr = { expr_attr with
          expr_type = Type.set_typed tp;
        } in

      App (Setenum, member_expr_list, expr_attr)
    
    | Var qual_ident, [] ->
      let qual_ident = 
        try
          SymbolTbl.fully_qualified qual_ident tbl 
        with Generic_Error msg -> Error.error (Expr.loc expr) (Printf.sprintf "%s\nExpr: %s \nTbl:%s" msg (Expr.to_string expr) (SymbolTbl.to_string tbl))
        in
      (match SymbolTbl.find tbl qual_ident with
      | Some (VarDecl var_decl) ->
        let tp = var_decl.var_type in
        let expr_attr = { expr_attr with
          expr_type = tp;
        } in

        App (Var qual_ident, [], expr_attr)
      
      | Some (Field field_def) -> 
        let tp = field_def.field_type in

        let expr_attr = { expr_attr with
          expr_type = tp;
        } in

        App (Var qual_ident, [], expr_attr)
      | Some tp_env -> Error.lexical_error (Expr.loc expr) ((QualIdent.to_string qual_ident ^ ": expected to be a VarDef instead of " ^ SymbolTbl.typing_env_to_string tp_env))
      | None -> Error.lexical_error (Expr.loc expr) ((QualIdent.to_string qual_ident ^ ": not found in TypingEnv"))
      )
    | Var _qual_ident, _expr_list -> Error.lexical_error (Expr.loc expr) ((Expr.constr_to_string constr ^ " expr takes no arguments"))

    | New, expr_list -> 
      let expr_list = List.map expr_list ~f:(fun expr -> process_expr expr tbl) in

      let _ = 
        List.map expr_list ~f:(fun expr ->
          let field_name = try 
            ASTUtil.expr_to_qual_ident expr
          with
            | Error.Msg(_loc, _msg) -> Error.type_error (Expr.loc expr) "Expected field name in new expression" 
          in

          match SymbolTbl.find tbl field_name with
          | Some (Field _) -> ()
          | _ -> Error.type_error (Expr.loc expr) "Expected field in symbolTbl for new expr arg."
        ) in
      let expr_attr = { expr_attr with
        expr_type = Type.ref;
      } in

      App (New, expr_list, expr_attr)
    )

  | Binder (binder, var_decl_list, inner_expr, expr_attr) ->

    let var_decl_list = List.map var_decl_list ~f:(fun var_decl -> ProcessTypeExpr.process_var_decl var_decl tbl) in

    let tbl = SymbolTbl.push tbl in
    let tbl = List.fold var_decl_list ~init:tbl ~f:(fun tbl' var_decl -> SymbolTbl.add tbl' (QualIdent.from_ident var_decl.var_name) (VarDecl var_decl)) in

    let inner_expr = process_expr inner_expr tbl in
    if Type.compare (Expr.to_type inner_expr) Type.bool = 0 || Type.compare (Expr.to_type inner_expr) Type.perm = 0 then
      let expr_attr = { expr_attr with
        expr_type = (Expr.to_type inner_expr);
      } in

      Binder (binder, var_decl_list, inner_expr, expr_attr)
    
    else
      Error.lexical_error (Expr.loc expr) ((Expr.to_string expr ^ ": inner expression should have type Bool or Perm, instead of " ^ Type.to_string (Expr.to_type inner_expr)))

module ProcessCallables = struct
  module DisambiguationTbl = struct
    type t = (ident ident_map) list  
    let push (disam_tbl: t) : t = Map.empty (module Ident) :: disam_tbl
    let pop (disam_tbl: t) : t = match disam_tbl with | [] -> raise (Generic_Error "Empty DisamTbl") | _ :: disam_tbl -> disam_tbl

    let add (disam_tbl: t) name new_name : t = match disam_tbl with
    | [] -> raise (Generic_Error "Empty DisamTbl; add failed")
    | hd :: tl -> (match Map.add hd ~key:name ~data:new_name with
      | `Ok hd -> hd :: tl
      | `Duplicate -> raise (Generic_Error (Ident.to_string name ^ ": DisamTbl add failed; found duplicate")))

    let rec find (disam_tbl: t) name =
      match disam_tbl with
      | [] -> None
      | map :: ts -> (
          match Map.find map name with | None -> find ts name | Some id -> Some id
        )

    let rec find_exn (disam_tbl: t) name =
      match disam_tbl with
      | [] -> raise (Generic_Error (Ident.to_string name ^ ": DisamTbl find_exn failed"))
      | map :: ts -> (
          match Map.find map name with | None -> find_exn ts name | Some id -> id
        )

    let add_var_decl (var_decl: Type.var_decl) (disam_tbl: t) : Type.var_decl * t = 
      let new_name = Ident.fresh var_decl.var_name.ident_name in
      let disam_tbl = add disam_tbl var_decl.var_name new_name in
      let var_decl = { var_decl with
        var_name = new_name;
      } in

      var_decl, disam_tbl
  end

  let rec disambiguate_expr (expr: expr) (disam_tbl: DisambiguationTbl.t) : expr = 
    match expr with
    | App (constr, expr_list, expr_attr) -> 
      let expr_list = List.map expr_list ~f:(fun expr -> disambiguate_expr expr disam_tbl) in

      (match constr with
      | Var qual_ident -> 
        let (qual_ident: qual_ident) = 
          if List.is_empty qual_ident.qual_path then 
            {
              qual_path = [];
              qual_base = (match DisambiguationTbl.find disam_tbl qual_ident.qual_base with
              | Some iden -> iden
              | None -> qual_ident.qual_base);
            }
          else
            qual_ident

        in
        App (Var qual_ident, expr_list, expr_attr)
      | _ -> App (constr, expr_list, expr_attr)
      )
    | Binder (binder, var_decl_list, expr, expr_attr) -> 
      Binder (binder, var_decl_list, disambiguate_expr expr disam_tbl, expr_attr)

  let disambiguate_process_expr (expr: expr) (tbl: SymbolTbl.t) (disam_tbl: DisambiguationTbl.t) : expr = 
    let expr = disambiguate_expr expr disam_tbl in
    let expr = process_expr expr tbl 
  
    in expr
          

  let process_stmt_spec (tbl: SymbolTbl.t) (disam_tbl: DisambiguationTbl.t) (spec: Stmt.spec) : Stmt.spec = { spec with
    spec_form = disambiguate_process_expr spec.spec_form tbl disam_tbl;
  }



  (* let rec purify_expr (expr: expr) (tbl: SymbolTbl.t) : Stmt.var_def list * expr = 
  (* Takes an expr, and returns a pure expression along with a set of temp variables that need to be defined  *)
  () *)

  (* let rec pre_process_stmt (stmt: Stmt.t) (tbl: SymbolTbl.t): Stmt.t list * var_decl list =
      (* Goes over the body of methods. Implements the following re-writes:
        1. Replaces any `var x : Type = value` stmts into the following two stmts: `var x : Type; x = value`. 
           This makes future processing simpler.
        2. Introduces temp variables for any complex arguments passed to callables, eg `func(1 + x)` becomes `var _temp = 1 + x; func(_temp)`
        3. It checks that inside ghost blocks, no callables or heap fields are referenced; ie only pure ghost stuff is allowed.
      *)
    
    match stmt.stmt_desc with
    | Block stmt_list ->
      let locals, stmt_list_list = List.fold_map stmt_list ~init:[] ~f:(fun locals stmt ->
        let stmt, locals' = pre_process_stmt stmt tbl in
          locals @ locals', stmt
      ) in
      [{stmt with stmt_desc = Block (List.concat stmt_list_list);}], locals

    | Basic basic_stmt -> 
      (match basic_stmt with
      | VarDef var_def ->
        (match var_def.var_init with
        | None -> [stmt], []
        | Some expr ->
          let stmt1: Stmt.t = { 
            stmt_desc = Basic (VarDef { var_def with var_init = None;});
            stmt_loc = stmt.stmt_loc
          } in

          let stmt2: Stmt.t = {
            stmt_desc = Basic (Assign { 
              assign_lhs = [
                App (Var (QualIdent.from_ident var_def.var_decl.var_name), [],
                (Expr.mk_attr stmt.stmt_loc var_def.var_decl.var_type))
              ]; 
              assign_rhs = expr});
            stmt_loc = stmt.stmt_loc
          } in

          [stmt1; stmt2], []
        )

      | Assume spec | Assert | _ -> ()

      )

    | Loop loop_desc -> 
      let loop_prebody_list, locals1 = pre_process_stmt loop_desc.loop_prebody tbl in
      let (loop_prebody: Stmt.t) = (match loop_prebody_list with
        | [ stmt ] -> stmt
        | stmt_list -> { stmt_desc = Block stmt_list; stmt_loc = loop_desc.loop_prebody.stmt_loc}) 
      in

      let loop_postbody_list, locals2 = pre_process_stmt loop_desc.loop_postbody tbl in
      let (loop_postbody: Stmt.t) = (match loop_postbody_list with
        | [ stmt ] -> stmt
        | stmt_list -> { stmt_desc = Block stmt_list; stmt_loc = loop_desc.loop_postbody.stmt_loc}
      ) in
      
      let loop_desc = { loop_desc with
      loop_prebody = loop_prebody;
      loop_postbody = loop_postbody;
      }
      in

      [{ stmt with stmt_desc = Loop loop_desc;}], locals1 @ locals2


    | Cond cond_desc -> ()
    | Ghost ghost_desc -> () *)
    
  
  let rec pre_process_stmt (stmt: Stmt.t) : Stmt.t list = 
    (* This function only takes stmts of type:
        var x : Type = val;
        
        and unfolds them into:
        var x : Type;
        x := val;
    *)
    match stmt.stmt_desc with
    | Block stmt_list ->
      let stmt_list = List.concat (List.map ~f:pre_process_stmt stmt_list) in
        [{stmt_desc = Block stmt_list; stmt_loc = stmt.stmt_loc;}]
    | Basic basic_stmt ->
      (match basic_stmt with
        | VarDef var_def -> 
          (match var_def.var_init with
          | None -> [stmt]
          | Some expr -> 
            let (var_def': Stmt.var_def) = {var_decl = var_def.var_decl; var_init = None} in
            let (stmt1: Stmt.t) = {stmt_desc = Basic (VarDef var_def'); stmt_loc = stmt.stmt_loc;} in
            let (var_expr: Expr.t) = App (Var (QualIdent.from_ident var_def.var_decl.var_name), [], {expr_loc = stmt.stmt_loc; expr_type = var_def.var_decl.var_type}) in
            let (assign_desc': Stmt.assign_desc) = {assign_lhs = [var_expr]; assign_rhs = expr} in
            let (stmt2: Stmt.t) = {stmt_desc = Basic (Assign assign_desc'); stmt_loc = stmt.stmt_loc;} in

            [stmt1; stmt2]
            
          )


        | _ -> [stmt]
      )
    | Loop loop_desc -> (
      let loop_prebody_list = pre_process_stmt loop_desc.loop_prebody in
      let loop_prebody' = (match loop_prebody_list with
        | [stmt'] -> stmt'
        | stmt_list -> {stmt_desc = Block stmt_list; stmt_loc = loop_desc.loop_prebody.stmt_loc;}
      ) in

      let loop_postbody_list = pre_process_stmt loop_desc.loop_postbody in
      let loop_postbody' = (match loop_postbody_list with
        | [stmt'] -> stmt'
        | stmt_list -> {stmt_desc = Block stmt_list; stmt_loc = loop_desc.loop_postbody.stmt_loc;}
      ) in


      let loop_desc' = { loop_desc with
            loop_prebody = loop_prebody';
            loop_postbody = loop_postbody';
      } in

      [{stmt with stmt_desc = Loop loop_desc';}]
      )

    | Cond cond_desc -> (
      let cond_then_list = pre_process_stmt cond_desc.cond_then in
      let cond_then' = (match cond_then_list with
        | [stmt'] -> stmt'
        | stmt_list -> {stmt_desc = Block stmt_list; stmt_loc = cond_desc.cond_then.stmt_loc;}
      ) in

      let cond_else_list = pre_process_stmt cond_desc.cond_else in
      let cond_else' = (match cond_else_list with
        | [stmt'] -> stmt'
        | stmt_list -> {stmt_desc = Block stmt_list; stmt_loc = cond_desc.cond_else.stmt_loc;}
      ) in

      let cond_desc' = { cond_desc with
            cond_then = cond_then';
            cond_else = cond_else';
      } in

      [{stmt with stmt_desc = Cond cond_desc';}]
    )

    | Ghost ghost_desc -> (
      let ghost_body_list = pre_process_stmt ghost_desc.ghost_body in
      let ghost_body' = (match ghost_body_list with
        | [stmt'] -> stmt'
        | stmt_list -> {stmt_desc = Block stmt_list; stmt_loc = ghost_desc.ghost_body.stmt_loc;}
      ) in

      let (ghost_desc': Stmt.ghost_desc) = { ghost_body = ghost_body';} in

      [{stmt with stmt_desc = Ghost ghost_desc';}]
    )

  let rec process_stmt (stmt: Stmt.t) (tbl: SymbolTbl.t) (disam_tbl: DisambiguationTbl.t) : Stmt.t * var_decl list * SymbolTbl.t * DisambiguationTbl.t = try

    let _stmt_list = pre_process_stmt stmt in
    let stmt = (match _stmt_list with
      | [stmt'] -> stmt'
      | stmt_list -> {stmt_desc = Block stmt_list; stmt_loc = stmt.stmt_loc;}
    ) in

    let stmt_desc, locals, tbl, disam_tbl =
    (match stmt.stmt_desc with
    | Block stmt_list -> 
      let tbl = SymbolTbl.push tbl in
      let disam_tbl = DisambiguationTbl.push disam_tbl in

      let (locals, tbl, disam_tbl), stmt_list = List.fold_map stmt_list ~init:([], tbl, disam_tbl) 
        ~f:(fun (locals, tbl, disam_tbl) stmt -> 
        
          let stmt, locals', tbl, disam_tbl = process_stmt stmt tbl disam_tbl in

          (locals @ locals', tbl, disam_tbl), stmt
        ) in

      let disam_tbl = DisambiguationTbl.pop disam_tbl in
      let tbl = SymbolTbl.pop tbl in
      
      (Stmt.Block stmt_list), locals, tbl, disam_tbl

    | Basic basic_stmt -> (match basic_stmt with
      | VarDef var_def -> 
        let var_decl = ProcessTypeExpr.process_var_decl var_def.var_decl tbl in
        let var_decl, disam_tbl = DisambiguationTbl.add_var_decl var_decl disam_tbl in
        let (var_def: Stmt.var_def) = (match var_def.var_init with
        | None -> 
          {var_decl = var_decl; var_init = None;}
        | Some expr ->
          let expr = disambiguate_expr expr disam_tbl in
          let expr = process_expr expr tbl in
          {var_decl = var_decl; var_init = Some expr}
        ) in

        let tbl = SymbolTbl.add tbl (QualIdent.from_ident var_decl.var_name) (VarDecl var_decl) in

        Basic (VarDef var_def), [var_decl], tbl, disam_tbl

      | Assume spec -> 
        let spec = process_stmt_spec tbl disam_tbl spec in
        Basic (Assume spec), [], tbl, disam_tbl

      | Assert spec -> 
        let spec = process_stmt_spec tbl disam_tbl spec in
        Basic (Assert spec), [], tbl, disam_tbl

      | Assign assign_desc ->
        (* THIS IS WHERE the RHS needs to be examined; *)

        (let open_au_call = QualIdent.from_ident (Ident.make "openAU" 0) in
        let commit_au_call = QualIdent.from_ident (Ident.make "commitAU" 0) in
        let bind_au_call = QualIdent.from_ident (Ident.make "bindAU" 0) in
        let abort_au_call = QualIdent.from_ident (Ident.make "abortAU" 0) in
        let fpu_call = QualIdent.from_ident (Ident.make "fpu" 0) in

        (match assign_desc.assign_rhs with
        | App (Call, proc :: args, expr_attr) ->
          let proc_qual_ident = ASTUtil.expr_to_qual_ident proc in

          if QualIdent.compare proc_qual_ident open_au_call = 0 then
            match args with
            | [ token ] ->
              let token_expr = disambiguate_process_expr token tbl disam_tbl in
              let au_token = ASTUtil.expr_to_ident token_expr
              
              in

              (match assign_desc.assign_lhs with
              | [] -> 
                let open_au = au_token in

                Basic (OpenAU open_au), [], tbl, disam_tbl
              | _ -> raise (Generic_Error ("openAU() does not take args on LHS."))
              )  

            | _ ->
                raise (Generic_Error ("openAU() called with incorrect number of arguments"))

          else if QualIdent.compare proc_qual_ident commit_au_call = 0 then
            match args with
            | token :: [] -> (
                match assign_desc.assign_lhs with
                | [] ->
                    let token_expr = disambiguate_process_expr token tbl disam_tbl in
                    let au_token = ASTUtil.expr_to_ident token_expr

                    in
                      
                    Basic (CommitAU au_token), [], tbl, disam_tbl

                | _ ->
                    raise (Generic_Error "incorrect number of LHS args to commitAU()")
                )
            | _ ->
                raise (Generic_Error "commitAU() called with incorrect number of arguments")

          else if QualIdent.compare proc_qual_ident bind_au_call = 0 then
            match args with
            | [] -> 
              (match assign_desc.assign_lhs with
              | [ token ] ->
                let token_expr = disambiguate_process_expr token tbl disam_tbl in
                Basic (BindAU (ASTUtil.expr_to_ident token_expr)), [], tbl, disam_tbl
              | _ ->
                raise (Generic_Error "incorrect number of bound_args to bindAU()")
              )

            | _ ->
                raise
                  (Generic_Error "bindAU() called with incorrect number of arguments")

          else if QualIdent.compare proc_qual_ident abort_au_call = 0 then
            match args with
            | [ token ] -> (
                match assign_desc.assign_lhs with
                | [] -> 
                  let token_expr = disambiguate_process_expr token tbl disam_tbl in
                  Basic (Stmt.AbortAU (ASTUtil.expr_to_ident token_expr)), [], tbl, disam_tbl
                | _ -> raise (Generic_Error "incorrect number of bound_args to abortAU()"))

            | _ -> raise (Generic_Error "abortAU() called without token")

          else if QualIdent.compare proc_qual_ident fpu_call = 0 then
            match assign_desc.assign_lhs, args with
            | [], [loc_expr; field_expr; val_expr] -> 
              let loc_expr = disambiguate_process_expr loc_expr tbl disam_tbl in
              let field_expr = disambiguate_process_expr field_expr tbl disam_tbl in
              let val_expr = disambiguate_process_expr val_expr tbl disam_tbl in

              if (Type.equal Type.ref (Expr.to_type loc_expr)) then
                (match SymbolTbl.find tbl (ASTUtil.expr_to_qual_ident field_expr) with
                | Some (Field field_def) -> (
                  (* The following additional call to process_type_expr is required because for fields with custom RAs, their types are stored as module names in typing env. The following call will convert it to appropriate rep type. *)
                  let field_type = ProcessTypeExpr.process_type_expr field_def.field_type tbl in

                  if (Type.equal (Type.join field_type (Expr.to_type val_expr)) field_type) then
                    let loc_qual_ident = ASTUtil.expr_to_qual_ident loc_expr in
                    let field_qual_ident = ASTUtil.expr_to_qual_ident field_expr in
                    let fpu_desc = {
                      Stmt.fpu_loc = loc_qual_ident;
                      fpu_field = field_qual_ident;
                      fpu_val = val_expr;
                    } in
                    Basic (Stmt.Fpu fpu_desc), [], tbl, disam_tbl
                  else
                    Error.type_error (Expr.loc assign_desc.assign_rhs) ("Field type mismatch. Field " ^ (Ident.to_string field_def.field_name) ^ " has type " ^ (Type.to_string field_def.field_type ^ "; received " ^ Type.to_string (Expr.to_type val_expr))))
                | Some _tp -> Error.type_error (Expr.loc assign_desc.assign_rhs) ("Expected Field in typing env. Found" ^ SymbolTbl.typing_env_to_string _tp)
                | None -> Error.type_error (Expr.loc assign_desc.assign_rhs) ("Field " ^ (Expr.to_string field_expr) ^ "not found in typing env")
                )
              else 
                Error.type_error (Expr.loc assign_desc.assign_rhs) @@ Printf.sprintf "Fpu stmt type mismatch."

            | _ ->
              raise (Generic_Error "fpu() called incorrectly")

          else
            let assign_lhs = List.map assign_desc.assign_lhs 
              ~f:(fun expr -> disambiguate_process_expr expr tbl disam_tbl) in

            let args = List.map args
              ~f:(fun expr -> disambiguate_expr expr disam_tbl) in

            (match (process_expr (App (Call, proc :: args, expr_attr)) tbl) with

            | App (Call, proc :: args, _expr_attr) ->

              let proc = disambiguate_expr proc disam_tbl in
              let proc_qual_ident = ASTUtil.expr_to_qual_ident proc in

              let (call_desc : Stmt.call_desc) =
                {
                  call_lhs =
                    List.map assign_lhs ~f:ASTUtil.expr_to_qual_ident;
                  call_name = proc_qual_ident;
                  call_args = args;
                }
              in

              Basic (Call call_desc), [] , tbl, disam_tbl

            | _ -> Error.lexical_error stmt.stmt_loc "Unexpected error."
            )

        | _ ->
          let assign_lhs = List.map assign_desc.assign_lhs 
            ~f:(fun expr -> 
              let expr = disambiguate_process_expr expr tbl disam_tbl in

              expr
          ) in

          let assign_rhs = 
            (let expr = disambiguate_process_expr assign_desc.assign_rhs tbl disam_tbl in
          
            expr
          ) in

          match assign_rhs with
          | App (New, field_args, _) ->
            (match assign_lhs with
            | [expr1] -> 
              let lhs_ident = try
                ASTUtil.expr_to_ident expr1
              with
              | Msg(_loc, _msg) -> Error.error (Expr.loc expr1) "Expected loc variable on lhs of new expr"
              in

              (if Type.equal (Type.meet (Expr.to_type expr1) (Expr.to_type assign_rhs)) Type.ref then
                let new_desc = 
                  {Stmt.new_lhs = lhs_ident;
                  new_args = field_args;
                  } in

                  Basic (New new_desc), [], tbl, disam_tbl
              else
                Error.type_error stmt.stmt_loc "New expr lhs rhs types don't match"

              )
            | _ -> Error.type_error stmt.stmt_loc "New expressions only take one expr on LHS"
            )
          | _ ->
            match assign_lhs with
            | [expr1] ->
              (* let tp1 = *)

              (try 
                does_expr_implement_type assign_rhs (Expr.to_type expr1) tbl
              with
              | Msg (_loc, msg) ->
                Error.type_error stmt.stmt_loc ("Assignment type doesn't match : " ^ msg));

              let (assign_desc: Stmt.assign_desc) = { 
                assign_lhs = assign_lhs;
                assign_rhs = assign_rhs;
              } in

              Basic (Assign assign_desc), [], tbl, disam_tbl

            (* TODO: Need to add support for product types for full functionality - eg match return types for callables which return multiple things *)

            | _ -> Error.unsupported_error stmt.stmt_loc "Assign stmts with multiple expr on LHS not currently supported"
          )
        )
      
      | Havoc expr_list ->
        let expr_list = List.map expr_list 
          ~f:(fun expr -> 
            let expr = disambiguate_expr expr disam_tbl in
            let expr = process_expr expr tbl 
          
            in expr
        ) in
        
        Basic (Havoc expr_list), [], tbl, disam_tbl

      | Return expr_list -> 
        let expr_list = List.map expr_list 
          ~f:(fun expr -> 
          let expr = disambiguate_expr expr disam_tbl in
          let expr = process_expr expr tbl 
        
          in expr
        ) in
      
        Basic (Return expr_list), [], tbl, disam_tbl

      | Fold fold_desc -> 
        let fold_expr = 
          (let expr = disambiguate_expr fold_desc.fold_expr disam_tbl in
          let expr = process_expr expr tbl 
        
          in expr
        ) in

        Basic (Fold {fold_expr}), [], tbl, disam_tbl

      | Unfold unfold_desc -> 
        let unfold_expr = 
          (let expr = disambiguate_expr unfold_desc.unfold_expr disam_tbl in
          let expr = process_expr expr tbl 
        
          in expr
        ) in

        Basic (Unfold {unfold_expr}), [], tbl, disam_tbl
      
      | OpenInv expr ->
        let expr = disambiguate_expr expr disam_tbl in
        let expr = process_expr expr tbl

        in 
        Basic (OpenInv expr), [], tbl, disam_tbl

      | CloseInv expr ->
        let expr = disambiguate_expr expr disam_tbl in
        let expr = process_expr expr tbl

        in 
        Basic (CloseInv expr), [], tbl, disam_tbl

      (* The following constructs are not expected here because the parser stores these commands as Assign stmts. 
        The job of this function is to intercept the Assign stmts with the specific expressions on the RHS, and then transform 
        them to the appropriate construct, ie Call, New, BindAU, OpenAU, AbortAU, CommitAU etc. 
        
        This function is not expected to go over these parts of the AST again. If the following constructs are
        discovered by this function, then something unexpected has happened. *)
      | Call _call_desc -> 
        let str = Print.string_of_format Stmt.pr_basic_stmt basic_stmt in
        raise (Generic_Error (str ^ ": InternalError: Did not expect call stmts in AST at this stage."))
      | New _new_desc ->
        let str = Print.string_of_format Stmt.pr_basic_stmt basic_stmt in
        raise (Generic_Error (str ^ ": InternalError: Did not expect new stmts in AST at this stage."))
      | BindAU _ident ->
        let str = Print.string_of_format Stmt.pr_basic_stmt basic_stmt in
        raise (Generic_Error (str ^ ": InternalError: Did not expect bindAU stmts in AST at this stage."))
      | OpenAU _open_au ->
        let str = Print.string_of_format Stmt.pr_basic_stmt basic_stmt in
        raise (Generic_Error (str ^ ": InternalError: Did not expect openAU stmts in AST at this stage."))
      | AbortAU _ident ->
        let str = Print.string_of_format Stmt.pr_basic_stmt basic_stmt in
        raise (Generic_Error (str ^ ": InternalError: Did not expect abortAU stmts in AST at this stage."))
      | CommitAU _commit_au ->
        let str = Print.string_of_format Stmt.pr_basic_stmt basic_stmt in
        raise (Generic_Error (str ^ ": InternalError: Did not expect commitAU stmts in AST at this stage."))
      | Inhale _expr -> 
        let str = Print.string_of_format Stmt.pr_basic_stmt basic_stmt in
        raise (Generic_Error (str ^ ": InternalError: Did not expect inhale stmts in AST at this stage."))
      | Exhale _expr -> 
        let str = Print.string_of_format Stmt.pr_basic_stmt basic_stmt in
        raise (Generic_Error (str ^ ": InternalError: Did not expect exhale stmts in AST at this stage."))
      | Fpu _fpu_desc -> 
        let str = Print.string_of_format Stmt.pr_basic_stmt basic_stmt in
        raise (Generic_Error (str ^ ": InternalError: Did not expect Fpu stmts in AST at this stage."))
      
      )

    | Loop loop_desc -> 
      let loop_contract = List.map loop_desc.loop_contract ~f:(process_stmt_spec tbl disam_tbl) in

      let tbl = SymbolTbl.push tbl in
      let disam_tbl = DisambiguationTbl.push disam_tbl in
      let loop_prebody, locals', tbl, disam_tbl = process_stmt loop_desc.loop_prebody tbl disam_tbl in
      let disam_tbl = DisambiguationTbl.pop disam_tbl in
      let tbl = SymbolTbl.pop tbl in

      let loop_test = disambiguate_process_expr loop_desc.loop_test tbl disam_tbl in

      let tbl = SymbolTbl.push tbl in
      let disam_tbl = DisambiguationTbl.push disam_tbl in
      let loop_postbody, locals'', tbl, disam_tbl = process_stmt loop_desc.loop_postbody tbl disam_tbl in
      let disam_tbl = DisambiguationTbl.pop disam_tbl in
      let tbl = SymbolTbl.pop tbl in

      (* Actually think about what variables need to be collected in `locals`. What if same variable is declared in multiple scopes in a callable, do all of them go in the `call_decl.call_decl_locals`? *)

      let (loop_desc: Stmt.loop_desc) = {
        loop_contract;
        loop_prebody;
        loop_test;
        loop_postbody;
      } in

      Loop loop_desc, locals' @ locals'', tbl, disam_tbl

    | Cond cond_desc ->
      let cond_test = disambiguate_process_expr cond_desc.cond_test tbl disam_tbl in

      let tbl = SymbolTbl.push tbl in
      let disam_tbl = DisambiguationTbl.push disam_tbl in
      let cond_then, locals', tbl, disam_tbl = process_stmt cond_desc.cond_then tbl disam_tbl in
      let disam_tbl = DisambiguationTbl.pop disam_tbl in
      let tbl = SymbolTbl.pop tbl in

      let tbl = SymbolTbl.push tbl in
      let disam_tbl = DisambiguationTbl.push disam_tbl in
      let cond_else, locals'', tbl, disam_tbl = process_stmt cond_desc.cond_else tbl disam_tbl in
      let disam_tbl = DisambiguationTbl.pop disam_tbl in
      let tbl = SymbolTbl.pop tbl in

      let (cond_desc: Stmt.cond_desc) = {
        cond_test;
        cond_then;
        cond_else;
      } in

      Cond cond_desc, locals' @ locals'', tbl, disam_tbl

    | Ghost ghost_desc -> 
      let tbl = SymbolTbl.push tbl in
      let disam_tbl = DisambiguationTbl.push disam_tbl in
      let ghost_body, locals, tbl, disam_tbl = process_stmt ghost_desc.ghost_body tbl disam_tbl in
      let disam_tbl = DisambiguationTbl.pop disam_tbl in
      let tbl = SymbolTbl.pop tbl in

      let (ghost_desc: Stmt.ghost_desc) = {
        ghost_body;
      } in

      Ghost ghost_desc, locals, tbl, disam_tbl
    ) in
  
    {stmt_desc = stmt_desc; stmt_loc = stmt.stmt_loc}, locals, tbl, disam_tbl

    with
      Generic_Error msg -> Error.lexical_error stmt.stmt_loc msg

  let process_callable ((mod_decl, tbl): Module.module_decl * SymbolTbl.t) (callable: Callable.t) : (Module.module_decl * SymbolTbl.t) * Callable.t =
    match callable with
      | FuncDef func_def ->
        (try
        let tbl = SymbolTbl.push tbl in
        let disam_tbl = (DisambiguationTbl.push []) in

        let disam_tbl, call_decl_locals_list = List.fold_map (Map.to_alist func_def.func_decl.call_decl_locals) ~init:disam_tbl ~f:(
          fun disam_tbl (_ident, var_decl) -> 
            let var_decl = ProcessTypeExpr.process_var_decl var_decl tbl in
            let var_decl', disam_tbl = DisambiguationTbl.add_var_decl var_decl disam_tbl in
            (disam_tbl, (var_decl'.var_name, var_decl'))
        ) in
        (* FuncDefs should not have any new call_decl_locals in body because they are expressions. That is, all call_decl_locals are the arguments it takes. These are being disambiguated in the above.*)
        
        let tbl = List.fold call_decl_locals_list ~init:tbl ~f:(fun tbl (iden, var_decl) -> SymbolTbl.add tbl (QualIdent.from_ident iden) (VarDecl var_decl)) in

        let func_decl = { func_def.func_decl with
          call_decl_formals = List.map func_def.func_decl.call_decl_formals ~f:(DisambiguationTbl.find_exn disam_tbl);
          call_decl_returns = List.map func_def.func_decl.call_decl_returns ~f:(DisambiguationTbl.find_exn disam_tbl);
          call_decl_locals = Map.of_alist_exn (module Ident) call_decl_locals_list;
          call_decl_precond = List.map func_def.func_decl.call_decl_precond ~f:(process_stmt_spec tbl disam_tbl);
          call_decl_postcond = List.map func_def.func_decl.call_decl_postcond ~f:(process_stmt_spec tbl disam_tbl);
        } in 

        let func_body = match func_def.func_body with
          | None -> None
          | Some expr -> Some (process_expr (disambiguate_expr expr disam_tbl) tbl) in

        let (func_def: Callable.func_def) = {
          func_decl = func_decl;
          func_body = func_body;
        } in

        let mod_decl = { mod_decl with
          mod_decl_callables = Map.set mod_decl.mod_decl_callables ~key:func_def.func_decl.call_decl_name ~data:func_def.func_decl;
        } in

        let tbl = SymbolTbl.pop tbl in
        let tbl = SymbolTbl.add tbl (QualIdent.from_ident func_def.func_decl.call_decl_name) (Callable func_def.func_decl) in
        
        (mod_decl, tbl), FuncDef func_def

        with
          Generic_Error msg -> Error.lexical_error func_def.func_decl.call_decl_loc msg)


      | ProcDef proc_def ->
        try 
        let tbl = SymbolTbl.push tbl in
        let disam_tbl = (DisambiguationTbl.push []) in 
        
        
        let disam_tbl, call_decl_locals_list = 
        try
        List.fold_map (Map.to_alist proc_def.proc_decl.call_decl_locals) ~init:disam_tbl ~f:(
          fun disam_tbl (_ident, var_decl) ->
            let var_decl = ProcessTypeExpr.process_var_decl var_decl tbl in
            let var_decl', disam_tbl = DisambiguationTbl.add_var_decl var_decl disam_tbl in
            (disam_tbl, (var_decl'.var_name, var_decl'))
        )
        with
          | Generic_Error msg -> Error.lexical_error proc_def.proc_decl.call_decl_loc ("LL"^ msg)

        in
         
        let tbl = List.fold call_decl_locals_list ~init:tbl ~f:(fun tbl (iden, var_decl) -> SymbolTbl.add tbl (QualIdent.from_ident iden) (VarDecl var_decl)) in

        let proc_decl = { proc_def.proc_decl with
          call_decl_formals = List.map proc_def.proc_decl.call_decl_formals ~f:(DisambiguationTbl.find_exn disam_tbl);
          (* TODO: Add a check to make sure that all the implicit ghost variables are declared at the end. *)
          call_decl_returns = List.map proc_def.proc_decl.call_decl_returns ~f:(DisambiguationTbl.find_exn disam_tbl);
          call_decl_locals = Map.of_alist_exn (module Ident) call_decl_locals_list;
          call_decl_precond = List.map proc_def.proc_decl.call_decl_precond ~f:(process_stmt_spec tbl disam_tbl);
          call_decl_postcond = List.map proc_def.proc_decl.call_decl_postcond ~f:(process_stmt_spec tbl disam_tbl);
        } in

        let proc_body, (locals: Type.var_decl list) = (match proc_def.proc_body with
        | None -> None, []
        | Some stmt -> 
          let stmt, locals, tbl', _disam_tbl = process_stmt stmt tbl disam_tbl in

          if SymbolTbl.equal tbl' tbl then
            Some stmt, locals
          else
            Error.lexical_error proc_decl.call_decl_loc "process_stmt returned a changed Typing Env tbl. Examine violation."
          ) 
        
        in
        
        let locals_map = List.fold locals ~init:(Map.empty (module Ident)) ~f:(fun map var_decl -> Map.add_exn map ~key:var_decl.var_name ~data:var_decl) in

        let proc_decl = {proc_decl with
            call_decl_locals = Map.merge_skewed proc_decl.call_decl_locals locals_map ~combine:(fun ~key:key _ -> raise (Generic_Error (Ident.to_string key ^ "duplicate var found in proc locals")));
        } in
        
        let (proc_def: Callable.proc_def) = {
          proc_decl = proc_decl;
          proc_body = proc_body;
        } in

        let mod_decl = { mod_decl with
          mod_decl_callables = Map.set mod_decl.mod_decl_callables ~key:proc_def.proc_decl.call_decl_name ~data:proc_def.proc_decl;
        } in

        let tbl = SymbolTbl.pop tbl in
        let tbl = SymbolTbl.add tbl (QualIdent.from_ident proc_def.proc_decl.call_decl_name) (Callable proc_def.proc_decl) in
        
        (mod_decl, tbl), ProcDef proc_def

        with
          Generic_Error msg -> Error.lexical_error proc_def.proc_decl.call_decl_loc (msg)

  
  let rec process_callables (callables: Callable.t list) (mod_decl: Module.module_decl) (tbl: SymbolTbl.t) : Callable.t list * Module.module_decl * SymbolTbl.t =
    let (mod_decl, tbl), callables = List.fold_map callables ~init:(mod_decl, tbl) ~f:process_callable in

    callables, mod_decl, tbl
      
end




module ProcessModule = struct
  let add_imports_to_tbl (imported_mod: Module.t) (orig_imported_mod: Module.t) (tbl: SymbolTbl.t) : SymbolTbl.t =
    let tbl = Map.fold (imported_mod.module_decl.mod_decl_fields) ~init:tbl ~f:(fun ~key:key ~data:data tbl -> SymbolTbl.add tbl (QualIdent.from_ident key) (Field data)) in

    let tbl = Map.fold (imported_mod.module_decl.mod_decl_mod_defs) ~init:tbl ~f:(fun ~key:mod_name ~data:_mod_decl tbl -> 
      let orig_mod = Module.find_mod orig_imported_mod.members.mod_defs mod_name in
      let new_mod = Module.find_mod imported_mod.members.mod_defs mod_name in
      SymbolTbl.add tbl (QualIdent.from_ident mod_name) (ModDecl (new_mod, orig_mod))) in

    let tbl = Map.fold (imported_mod.module_decl.mod_decl_mod_aliases) ~init:tbl ~f:(fun ~key:key ~data:data tbl -> SymbolTbl.add tbl (QualIdent.from_ident key) (ModAlias data)) in

    let tbl = Map.fold (imported_mod.module_decl.mod_decl_types) ~init:tbl ~f:(fun ~key:key ~data:data tbl -> SymbolTbl.add tbl (QualIdent.from_ident key) (TypeAlias data)) in

    let tbl = Map.fold (imported_mod.module_decl.mod_decl_callables) ~init:tbl ~f:(fun ~key:key ~data:data tbl -> SymbolTbl.add tbl (QualIdent.from_ident key) (Callable data)) in

    let tbl = Map.fold (imported_mod.module_decl.mod_decl_vars) ~init:tbl ~f:(fun ~key:key ~data:data tbl -> SymbolTbl.add tbl (QualIdent.from_ident key) (VarDecl data)) in

    tbl

  let rec process_imports (import_directives: Module.import_directive list) (mod_decl: Module.module_decl) (tbl: SymbolTbl.t) : Module.module_decl * SymbolTbl.t =
    
    let merging_function ~key:_ v _ = v

    in

    match import_directives with
    | [] -> mod_decl, tbl
    | imp :: import_directives -> (
      match imp with
      | ModImport tp_exp ->
        (match (SymbolTbl.find tbl (ASTUtil.type_expr_to_qual_ident tp_exp)) with
        | Some (ModDecl (imported_mod, orig_imp_mod)) -> 

          let mod_decl = { mod_decl with
            mod_decl_fields = Map.merge_skewed mod_decl.mod_decl_fields imported_mod.module_decl.mod_decl_fields ~combine:merging_function;
            mod_decl_mod_defs = Map.merge_skewed mod_decl.mod_decl_mod_defs imported_mod.module_decl.mod_decl_mod_defs ~combine:merging_function;
            mod_decl_mod_aliases = Map.merge_skewed mod_decl.mod_decl_mod_aliases imported_mod.module_decl.mod_decl_mod_aliases ~combine:merging_function;
            mod_decl_types = Map.merge_skewed mod_decl.mod_decl_types imported_mod.module_decl.mod_decl_types ~combine:merging_function;
            mod_decl_callables = Map.merge_skewed mod_decl.mod_decl_callables imported_mod.module_decl.mod_decl_callables ~combine:merging_function;
            mod_decl_vars = Map.merge_skewed mod_decl.mod_decl_vars imported_mod.module_decl.mod_decl_vars  ~combine:merging_function;
          } in

          let tbl = add_imports_to_tbl imported_mod orig_imp_mod tbl in

          process_imports import_directives mod_decl tbl
          
        | _ -> Error.lexical_error Loc.dummy ("Import " ^ Type.to_string tp_exp ^ " could not be processed." ^ "\n Tbl: \n" ^ SymbolTbl.to_string tbl)
        )
        
      | MemImport _qual_ident ->
        (Error.unsupported_error Loc.dummy "MemImports not supported")
        (* match (SymbolTbl.find tbl qual_ident) with
        | None -> Error.lexical_error Loc.dummy ("Import " ^ QualIdent.to_string qual_ident ^ " not found")
        | Some (TypeAlias tp_alias) ->
          let mod_decl = { mod_decl with
            mod_decl_types = Map.add_exn mod_decl.mod_decl_types ~key:tp_alias.type_alias_name ~data: tp_alias;
          } in 

          let tbl = SymbolTbl.add tbl (QualIdent.from_ident tp_alias.type_alias_name) (TypeAlias tp_alias) in

          process_imports import_directives mod_decl tbl

        | Some (Callable call_decl) -> let mod_decl = { mod_decl with
            mod_decl_callables = Map.add_exn mod_decl.mod_decl_callables ~key:call_decl.call_decl_name ~data:call_decl;
          } in 

          let tbl = SymbolTbl.add tbl (QualIdent.from_ident call_decl.call_decl_name) (Callable call_decl) in

          process_imports import_directives mod_decl tbl

        | Some (ModAlias mod_alias) -> let mod_decl = { mod_decl with
            mod_decl_mod_aliases = Map.add_exn mod_decl.mod_decl_mod_aliases ~key:mod_alias.mod_alias_name ~data:mod_alias;
          } in

          let tbl = SymbolTbl.add tbl (QualIdent.from_ident mod_alias.mod_alias_name) (ModAlias mod_alias) in

          process_imports import_directives mod_decl tbl

        | Some (ModDecl (mod_decl, _orig_mod)) -> let mod_decl = { mod_decl with
            mod_decl_mod_defs = Map.add_exn mod_decl.mod_decl_mod_defs ~key:mod_decl.mod_decl_name ~data:mod_decl;
          } in

          let tbl = SymbolTbl.add tbl (QualIdent.from_ident mod_decl.mod_decl_name) (ModDecl (mod_decl, _orig_mod)) in

          process_imports import_directives mod_decl tbl

        | Some (VarDecl var_decl) -> let mod_decl = { mod_decl with
            mod_decl_vars = Map.add_exn mod_decl.mod_decl_vars ~key:var_decl.var_name ~data:var_decl;
          } in

          let tbl = SymbolTbl.add tbl (QualIdent.from_ident var_decl.var_name) (VarDecl var_decl) in

          process_imports import_directives mod_decl tbl

        | Some (Field field_def) -> let mod_decl = { mod_decl with
            mod_decl_fields = Map.add_exn mod_decl.mod_decl_fields ~key:field_def.field_name ~data:field_def;
          } in

          let tbl = SymbolTbl.add tbl (QualIdent.from_ident field_def.field_name) (Field field_def) in

          process_imports import_directives mod_decl tbl

        | _ -> Error.error_simple @@ Printf.sprintf "MemImport of unsupported element '%s' found. Error." (QualIdent.to_string qual_ident) *)
    )

  let rec process_types (type_aliases: Module.type_alias list) (mod_decl: Module.module_decl) (tbl: SymbolTbl.t) : Module.type_alias list * Module.module_decl * SymbolTbl.t = match type_aliases with 
  | [] -> [], mod_decl, tbl
  | tp_alias :: type_aliases ->
    match tp_alias.type_alias_def with
    | None -> let tbl = SymbolTbl.add tbl (QualIdent.from_ident tp_alias.type_alias_name) (TypeAlias tp_alias) in

      let (type_alias_list, mod_decl, tbl) = process_types type_aliases mod_decl tbl in

      tp_alias :: type_alias_list, mod_decl, tbl

    | Some tp_expr ->

      let tp_expr, tbl = 
        (match tp_expr with
        | App (Data variant_decl_list, [], _tp_attr) ->
          (* _constr_map is constructed just to make sure no duplicate constructors are used in data type declaration. *)
          let _constr_map = List.fold variant_decl_list ~init:(Map.empty (module Ident))  ~f:(fun mp variant_decl -> 
            List.fold variant_decl.variant_args ~init:mp ~f:(fun mp var_arg ->
              match
                (Map.add mp ~key:var_arg.var_name ~data:var_arg)
              with
              | `Ok mp -> mp
              | `Duplicate -> Error.error (Type.to_loc tp_expr) @@ Printf.sprintf "Duplicate constructor found in data type %s" (Type.to_string tp_expr)
              )
          ) in

          let variant_decl_list = List.map variant_decl_list ~f:(fun variant_decl -> 
            let args = List.map variant_decl.variant_args ~f:(fun var_decl -> ProcessTypeExpr.process_var_decl var_decl tbl) in

            { variant_decl with
              variant_args = args
            }
          ) in

          let fully_qualified_tp_name = SymbolTbl.fully_qualified (QualIdent.from_ident tp_alias.type_alias_name) tbl in

          let tbl = List.fold variant_decl_list ~init:tbl ~f:(fun tbl variant_decl -> 
            let tbl = List.fold variant_decl.variant_args ~init:tbl ~f:(fun tbl var_arg ->
              let (data_type_destr: SymbolTbl.data_type_destr) = {
                destr_name = var_arg.var_name;
                destr_arg = App (Var fully_qualified_tp_name, [], _tp_attr);
                destr_return_type = var_arg.var_type;
              }  in

              SymbolTbl.add tbl (QualIdent.from_ident var_arg.var_name) (DataTypeDestr data_type_destr)
            ) in

            let (data_type_constr: SymbolTbl.data_type_constr) = {
              constr_name = variant_decl.variant_name;
              constr_return_type = App (Var fully_qualified_tp_name, [], _tp_attr);
              constr_args = variant_decl.variant_args;
            }

            in

            SymbolTbl.add tbl (QualIdent.from_ident variant_decl.variant_name) (DataTypeConstr data_type_constr)          
          ) in

          Type.App (Data variant_decl_list, [], _tp_attr), tbl

          
        | App (Data _variant_decl_list, _, _tp_attr) ->
          Error.error (Type.to_loc tp_expr) ("Data types don't take arguments")

        | _ ->
          let tp_expr = try 
            ProcessTypeExpr.process_type_expr tp_expr tbl 
          with (Generic_Error msg) -> Error.lexical_error tp_alias.type_alias_loc msg
          in

          tp_expr, tbl

        ) in

        let tp_alias = { tp_alias with
          type_alias_def = Some tp_expr;
        } in

        let mod_decl = { mod_decl with
          mod_decl_types = Map.set mod_decl.mod_decl_types ~key:tp_alias.type_alias_name ~data: tp_alias;
        } in

        let tbl = SymbolTbl.add tbl (QualIdent.from_ident tp_alias.type_alias_name) (TypeAlias tp_alias) in

        let (type_alias_list, mod_decl, tbl) = process_types type_aliases mod_decl tbl in

        tp_alias :: type_alias_list, mod_decl, tbl

  let rec process_fields (fields: Module.field_def list) (mod_decl: Module.module_decl) (tbl: SymbolTbl.t) : Module.field_def list * Module.module_decl * SymbolTbl.t =
    match fields with
    | [] -> [], mod_decl, tbl
    | field :: fields ->
      let tp_expr = 
        match field.field_type with
        | App (Var qual_ident, [], tp_attr) ->
          let fully_qualified_qual_ident = SymbolTbl.fully_qualified qual_ident tbl in
          (match SymbolTbl.find tbl fully_qualified_qual_ident with
          | Some RAModDecl _ ->
            Type.App (Var fully_qualified_qual_ident, [], tp_attr)

          | _ -> 
            try
              ProcessTypeExpr.process_type_expr field.field_type tbl
            with (Generic_Error msg) -> Error.lexical_error field.field_loc msg
          )
        
        | _ ->  
          try
            ProcessTypeExpr.process_type_expr field.field_type tbl
          with (Generic_Error msg) -> Error.lexical_error field.field_loc msg
      in

      let field = { field with
        field_type = tp_expr;
      } in

      let mod_decl = {mod_decl with
        mod_decl_fields = Map.set mod_decl.mod_decl_fields ~key:field.field_name ~data:field
      } in

      let tbl = SymbolTbl.add tbl (QualIdent.from_ident field.field_name) (Field field) in

      let (fields, mod_decl, tbl) = process_fields fields mod_decl tbl in

      field :: fields, mod_decl, tbl

  let rec process_vars (vars: Stmt.var_def list) (mod_decl: Module.module_decl) (tbl: SymbolTbl.t) : Stmt.var_def list * Module.module_decl * SymbolTbl.t = 
    match vars with
    | [] -> [], mod_decl, tbl
    | var :: vars ->
      let var_decl = try
        ProcessTypeExpr.process_var_decl var.var_decl tbl
      with (Generic_Error msg) -> Error.lexical_error var.var_decl.var_loc msg
      in

      let (var_expr: expr option) =  match var.var_init with 
      | None -> None
      | Some expr -> 
        let expr = process_expr expr tbl in

        (try 
          does_expr_implement_type expr var_decl.var_type tbl
        with
        | Msg (_loc, msg) ->
          Error.type_error var_decl.var_loc ("Var assignment type doesn't match : " ^ msg));
          
        Some expr

      in

      let (var: Stmt.var_def) = {
        var_decl = var_decl;
        var_init = var_expr
      } in

      let mod_decl = { mod_decl with
        mod_decl_vars = Map.set mod_decl.mod_decl_vars ~key:var.var_decl.var_name ~data:var.var_decl;
      } in

      let tbl = SymbolTbl.add tbl (QualIdent.from_ident var.var_decl.var_name) (VarDecl var.var_decl) in

      let (vars, mod_decl, tbl) = process_vars vars mod_decl tbl in

      var :: vars, mod_decl, tbl


  let rec instantiate_module (m: Module.t) (tp_args: type_expr list) (tbl: SymbolTbl.t) : Module.t * Module.t * SymbolTbl.t = 
    let rec instantiate_mod_helper (m: Module.t) (tp_args: type_expr list) (tbl: SymbolTbl.t): Module.t =
      (match (tp_args, m.module_decl.mod_decl_formals) with
      | [], _ -> m
      | _tp_arg :: _, [] -> raise (Generic_Error (Ident.to_string m.module_decl.mod_decl_name ^ " initialized with too many parameters"))
      | tp_arg :: tp_args, formal :: formals ->


        let formal_mod_alias = (match Map.find m.module_decl.mod_decl_mod_aliases formal with 
        | None -> raise (Generic_Error "Formal arg not found; likely parser error")
        | Some mod_alias -> mod_alias) in

        if Type.is_any formal_mod_alias.mod_alias_type || true then
          (* TODO: || does_module_implement_module (type_expr_to_mod_decl tp_arg tbl) (type_expr_to_mod_decl formal_mod_alias.mod_alias_type tbl)*)

          let new_alias = {formal_mod_alias with mod_alias_def = Some tp_arg} in

          let mod_decl = {m.module_decl with
            mod_decl_formals = formals;
            mod_decl_mod_aliases = Map.set m.module_decl.mod_decl_mod_aliases ~key: formal ~data:new_alias
          } in

          let members = {m.members with
          mod_aliases = new_alias :: m.members.mod_aliases;
          } in

          let (new_mod: Module.t) = {
            module_decl = mod_decl;
            members = members;
            interface = false;
            obligations = m.obligations;
          } in

          instantiate_mod_helper new_mod tp_args tbl
        
        else
          raise (Generic_Error ("Argument " ^ Type.to_string tp_arg ^ " does not match type " ^ Type.to_string formal_mod_alias.mod_alias_type ^ " for Module " ^ Ident.to_string m.module_decl.mod_decl_name))

      
    ) in


    let instantiated_mod = instantiate_mod_helper m tp_args tbl in

    let processed_mod, tbl = process_module instantiated_mod tbl in

    processed_mod, instantiated_mod, tbl
     
  and does_module_implement_module (_mod_decl: Module.module_decl) (_implemented_mod_decl: Module.module_decl) : bool = 
    true
    (* TODO *)

  and module_alias_to_module (mod_alias: Module.module_alias) (tbl: SymbolTbl.t) : Module.t * Module.t * bool * SymbolTbl.t =
    let tp_expr = 
      match mod_alias.mod_alias_def with
      | None -> mod_alias.mod_alias_type
      | Some tp_expr -> tp_expr

    in

    (match tp_expr with
      | App (Var mod_name, tp_args, _) ->
        let orig_mod, is_ra = 
        (match SymbolTbl.find tbl mod_name with
        | Some (ModDecl (_mod, orig_mod)) -> orig_mod, false
        | Some (RAModDecl (_mod, orig_mod)) -> orig_mod, true
        
        | Some (ModAlias mod_alias) ->
          Error.error mod_alias.mod_alias_loc "Error: Found ModAlias in SymbolTbl for definition of mod_alias.";
        
        | _ -> Error.error mod_alias.mod_alias_loc @@ (Printf.sprintf "Unexpected elem found in typing env for type_expr %s of modAlias.\n\nTbl:%s" (Type.to_string tp_expr) (SymbolTbl.to_string tbl))
        ) in

        let new_mod = {orig_mod with
          module_decl = {orig_mod.module_decl with mod_decl_name = mod_alias.mod_alias_name;}
        } in

        let inst_mod, orig_mod, tbl = instantiate_module new_mod tp_args tbl in

        inst_mod, orig_mod, is_ra, tbl

      | _ -> Error.error mod_alias.mod_alias_loc "Unexpected type_expr found in mod_alias_type for type of modAlias."
      )

  and process_mod_alias_tp_expr (tp_expr: type_expr) (tbl: SymbolTbl.t) (loc: Util.Loc.t): type_expr =
    (* This function is separate from process_tp_expr is because in normal code, a Var type_expr is treated differently from a Var type_expr used as argument in mod_alias. *)
  match tp_expr with
  | App (Var qual_ident, tp_args, tp_attr) ->

    let tp_args = List.map tp_args ~f:(fun tp_arg -> process_mod_alias_tp_expr tp_arg tbl loc) in

    let fully_qualified_ident = 
      try 
        SymbolTbl.fully_qualified qual_ident tbl 
      with 
      | Generic_Error msg -> Error.error (Type.to_loc tp_expr) @@ Printf.sprintf "%s\nTbl:%s" msg (SymbolTbl.to_string tbl)
      in
    (match SymbolTbl.find tbl fully_qualified_ident with
    | Some (ModDecl _) | Some (TypeAlias _) | Some (ModAlias _) | (Some RAModDecl _) ->
      Type.App (Var fully_qualified_ident, tp_args, tp_attr)
    | _ -> Error.error loc "Unexpected argument given in ModAlias"
    )
  
  | _ -> ProcessTypeExpr.process_type_expr tp_expr tbl
      
  
  and process_module_alias (mod_alias: Module.module_alias) (mod_decl: Module.module_decl) (tbl: SymbolTbl.t) : Module.module_alias * Module.module_decl * SymbolTbl.t = 
    (* Mod_aliases will be instantiated to appropriate module_decl, and their expanded module_decl will be stored to the symbol tbl. In the actual AST itself, they will remain as mod_aliases. *)

    let mod_alias_type = 
      (match mod_alias.mod_alias_type with
      | App (Any, _, _) -> 
        mod_alias.mod_alias_type
      | App (Var _mod_name, _tp_args, _tp_attr) ->
        process_mod_alias_tp_expr mod_alias.mod_alias_type tbl mod_alias.mod_alias_loc

      | _ -> Error.error (mod_alias.mod_alias_loc) "Unexpected Type found in mod_alias"
      ) in

    let mod_alias_def = 
      (match mod_alias.mod_alias_def with
      | None -> None
      | Some tp_expr ->
        Some (process_mod_alias_tp_expr tp_expr tbl mod_alias.mod_alias_loc)
      )

    in

    let mod_alias = { mod_alias with
      mod_alias_type = mod_alias_type;
      mod_alias_def = mod_alias_def;
    } in

    (* TODO: Make sure mod_alias_def actually implements mod_alias_type *)

    let derived_mod, orig_derived_module, is_ra, tbl = module_alias_to_module mod_alias tbl in

    let tbl = SymbolTbl.add tbl (QualIdent.from_ident mod_alias.mod_alias_name) (if is_ra then RAModDecl (derived_mod, orig_derived_module) else (ModDecl (derived_mod, orig_derived_module))) in

    let mod_decl = { mod_decl with
      mod_decl_mod_aliases = Map.set mod_decl.mod_decl_mod_aliases ~key:mod_alias.mod_alias_name ~data:mod_alias;
    } in

    mod_alias, mod_decl, tbl
  


  and process_mod_aliases (mod_aliases: Module.module_alias list) (mod_decl: Module.module_decl) (tbl: SymbolTbl.t) : Module.module_alias list * Module.module_decl * SymbolTbl.t = 
    let (mod_decl, tbl), mod_aliases = List.fold_map mod_aliases ~init:(mod_decl, tbl) ~f:(fun (mod_decl, tbl) mod_alias ->
      let mod_alias, mod_decl, tbl = process_module_alias mod_alias mod_decl tbl in
      (mod_decl, tbl), mod_alias
    ) in

    mod_aliases, mod_decl, tbl

  and process_module (m: Module.t) (tbl: SymbolTbl.t) : Module.t * SymbolTbl.t =

    let orig_mod = m in

    let tbl = SymbolTbl.push_name m.module_decl.mod_decl_name tbl in

    (* The following add_imports_to_tbl call is present to allow mutual recursion inside a module. *)
    let tbl = add_imports_to_tbl m m tbl in

    let mod_decl = m.module_decl in

    let formal_args_mod_aliases = List.map mod_decl.mod_decl_formals ~f:(fun mod_name -> 
      Map.find_exn mod_decl.mod_decl_mod_aliases mod_name) 
    in

    let _mod_aliases, mod_decl, tbl = process_mod_aliases formal_args_mod_aliases mod_decl tbl in
    (* This is instantiating all formal arguments to the module. The process_mod_aliases is primarily called to add the requisite members to the tbl for processing the rest of the module. (It also fully modifies the mod_decl by expanding the modules names referenced in mod_aliases to fully quantified names.) The returned mod_aliases are not stored.  *)

    let mod_aliases, mod_decl, tbl = process_mod_aliases m.members.mod_aliases mod_decl tbl in

    let mod_decl, tbl = process_imports m.members.imports mod_decl tbl in

    let type_aliases, mod_decl, tbl = process_types m.members.types mod_decl tbl in

    let fields, mod_decl, tbl = process_fields m.members.fields mod_decl tbl in

    let vars, mod_decl, tbl = process_vars m.members.vars mod_decl tbl in

    let call_defs, mod_decl, tbl = ProcessCallables.process_callables m.members.call_defs mod_decl tbl in
    
    let mod_defs, mod_decl, tbl = List.fold m.members.mod_defs ~init:([], mod_decl, tbl) 
    ~f:(fun (mod_defs, parent_mod_decl, tbl) (mod_def: Module.t) -> 

      let (mod_def, tbl) = process_module mod_def tbl in

      let (parent_mod_decl': Module.module_decl) = 
      let open Module in  
      { parent_mod_decl with
        mod_decl_mod_defs = Map.set parent_mod_decl.mod_decl_mod_defs ~key:mod_def.module_decl.mod_decl_name ~data:mod_def.module_decl;
      } in

      (mod_defs @ [mod_def], parent_mod_decl', tbl)
    )

    in

    let mod_decl, inherited_fields, inherited_types, inherited_vars, inherited_call_defs, tbl, does_mod_impl_ra = List.fold mod_decl.mod_decl_returns ~init:(mod_decl, [], [], [], [], tbl, false) ~f:(fun (mod_decl, inherited_fields, inherited_types, inherited_vars, inherited_call_defs, tbl, is_ra) tp_expr ->
      (
        let tp_expr = process_mod_alias_tp_expr tp_expr tbl (Type.to_loc tp_expr) in 
        let (impl_alias: Module.module_alias) = {
          mod_alias_name = mod_decl.mod_decl_name;
          mod_alias_type = tp_expr;
          mod_alias_def = None;
          mod_alias_loc = Type.to_loc tp_expr;
        } in

        let tbl' = SymbolTbl.pop tbl in

        (* The above pop is required because otherwise the instantiated module is instantiated in the wrong namespace. Eg, if the current module is M, impl_mod will be called $Prog.M.M, instead of $Prog.M like we want. *)

        let impl_mod, _, is_ra', _ = module_alias_to_module impl_alias tbl' in
        

        let inherited_fields, mod_decl, tbl = Map.fold impl_mod.module_decl.mod_decl_fields ~init:(inherited_fields, mod_decl, tbl) ~f:(fun ~key:field_name ~data:field_def (inherited_fields, mod_decl, tbl) ->
          match Map.find mod_decl.mod_decl_fields field_name with
          | None -> 
            let mod_decl = { mod_decl with
              mod_decl_fields = Map.set mod_decl.mod_decl_fields ~key:field_def.field_name ~data:field_def;
            } in

            let tbl = SymbolTbl.add tbl (QualIdent.from_ident field_def.field_name) (Field field_def) in

            field_def :: inherited_fields, mod_decl, tbl
          | Some field_def' -> 
            if Type.equal field_def'.field_type field_def.field_type then 
              (inherited_fields, mod_decl, tbl)
            else
              Error.error (Type.to_loc tp_expr) @@ Printf.sprintf "Module %s implementation of field %s incompatible with %s" (Ident.to_string mod_decl.mod_decl_name) (Ident.to_string field_name) (Type.to_string tp_expr)
        ) in

        let inherited_types, mod_decl, tbl = Map.fold impl_mod.module_decl.mod_decl_types ~init:(inherited_types, mod_decl, tbl) ~f:(fun ~key:type_name ~data:type_def (inherited_types, mod_decl, tbl) ->
          match Map.find mod_decl.mod_decl_types type_name with
          | None -> 
            let mod_decl = { mod_decl with
              mod_decl_types = Map.set mod_decl.mod_decl_types ~key:type_def.type_alias_name ~data: type_def; 
            } in

            let tbl = SymbolTbl.add tbl (QualIdent.from_ident type_def.type_alias_name) (TypeAlias type_def) in
            type_def :: inherited_types, mod_decl, tbl
            (* Error.error (Type.to_loc tp_expr) @@ Printf.sprintf "Module %s does not implement type %s -- incompatible with %s" (Ident.to_string mod_decl.mod_decl_name) (Ident.to_string type_name) (Type.to_string tp_expr) *)
          | Some type_def' -> 
            match type_def'.type_alias_def, type_def.type_alias_def with
            | None, None -> (inherited_types, mod_decl, tbl)
            | Some _tp_expr, None -> (inherited_types, mod_decl, tbl)
            | None, Some tp_expr1 -> Error.error (Type.to_loc tp_expr1) @@ Printf.sprintf "Module %s does not implement type %s -- incompatible with %s" (Ident.to_string mod_decl.mod_decl_name) (Ident.to_string type_name) (Type.to_string tp_expr)
            | Some tp_expr1, Some tp_expr2 ->
              if Type.equal tp_expr1 tp_expr2 then 
                (inherited_types, mod_decl, tbl)
              else
                Error.error (Type.to_loc tp_expr) @@ Printf.sprintf "Module %s implementation of type %s incompatible with %s" (Ident.to_string mod_decl.mod_decl_name) (Ident.to_string type_name) (Type.to_string tp_expr)
        ) in

        let inherited_vars, mod_decl, tbl = Map.fold impl_mod.module_decl.mod_decl_vars ~init:(inherited_vars, mod_decl, tbl) ~f:(fun ~key:var_name ~data:var_decl (inherited_vars, mod_decl, tbl) ->
          match Map.find mod_decl.mod_decl_vars var_name with
          | None -> 
            let var_def = Module.find_var impl_mod.members.vars var_name in
            
            let mod_decl = { mod_decl with
            mod_decl_vars = Map.set mod_decl.mod_decl_vars ~key:var_def.var_decl.var_name ~data:var_def.var_decl;
          } in
    
          let tbl = SymbolTbl.add tbl (QualIdent.from_ident var_def.var_decl.var_name) (VarDecl var_def.var_decl) in

            var_def :: inherited_vars, mod_decl, tbl
            (* Error.error (Type.to_loc tp_expr) @@ Printf.sprintf "Module %s does not implement var %s -- incompatible with %s" (Ident.to_string mod_decl.mod_decl_name) (Ident.to_string var_name) (Type.to_string tp_expr) *)
          | Some var_decl' -> 
            
            if Type.equal var_decl'.var_type var_decl.var_type then 
              (inherited_vars, mod_decl, tbl)
            else
              Error.error (Type.to_loc tp_expr) @@ Printf.sprintf "Module %s type of var %s incompatible with %s" (Ident.to_string mod_decl.mod_decl_name) (Ident.to_string var_name) (Type.to_string tp_expr)
        ) in

        let inherited_call_defs, mod_decl, tbl = Map.fold impl_mod.module_decl.mod_decl_callables ~init:(inherited_call_defs, mod_decl, tbl) ~f:(fun ~key:call_name ~data:call_decl (inherited_call_defs, mod_decl, tbl) ->
          match Map.find mod_decl.mod_decl_callables call_name with
          | None -> 
            let impl_callable = (Module.find_callable impl_mod.members.call_defs call_name) in
            (match impl_callable with
            | ProcDef proc_def ->
              (match proc_def.proc_body with
              | Some _ -> 
                let mod_decl = { mod_decl with
                  mod_decl_callables = Map.set mod_decl.mod_decl_callables ~key:proc_def.proc_decl.call_decl_name ~data:proc_def.proc_decl;
                } in

                let tbl = SymbolTbl.add tbl (QualIdent.from_ident proc_def.proc_decl.call_decl_name) (Callable proc_def.proc_decl) in

                impl_callable :: inherited_call_defs, mod_decl, tbl
              | None ->
                if m.interface then
                  let mod_decl = { mod_decl with
                    mod_decl_callables = Map.set mod_decl.mod_decl_callables ~key:proc_def.proc_decl.call_decl_name ~data:proc_def.proc_decl;
                  } in

                  let tbl = SymbolTbl.add tbl (QualIdent.from_ident proc_def.proc_decl.call_decl_name) (Callable proc_def.proc_decl) in

                  impl_callable :: inherited_call_defs, mod_decl, tbl
                else
                  (match proc_def.proc_decl.call_decl_kind with
                  | Lemma -> 
                    let proc_def = { proc_def with
                      proc_body = Some (Stmt.mk_skip (Type.to_loc tp_expr));
                    } in

                    
                    let mod_decl = { mod_decl with
                      mod_decl_callables = Map.set mod_decl.mod_decl_callables ~key:proc_def.proc_decl.call_decl_name ~data:proc_def.proc_decl;
                    } in

                    let tbl = SymbolTbl.add tbl (QualIdent.from_ident proc_def.proc_decl.call_decl_name) (Callable proc_def.proc_decl) in

                    ProcDef proc_def :: inherited_call_defs, mod_decl, tbl

                  | _ -> Error.error (Type.to_loc tp_expr) @@ Printf.sprintf "Module %s does not implement callable %s -- incompatible with %s" (Ident.to_string mod_decl.mod_decl_name) (Ident.to_string call_name) (Type.to_string tp_expr)
                  )
                )
                
            | FuncDef func_def ->
              (match func_def.func_body with
              | Some _ -> 
                let mod_decl = { mod_decl with
                  mod_decl_callables = Map.set mod_decl.mod_decl_callables ~key:func_def.func_decl.call_decl_name ~data:func_def.func_decl;
                } in

                let tbl = SymbolTbl.add tbl (QualIdent.from_ident func_def.func_decl.call_decl_name) (Callable func_def.func_decl) in

                impl_callable :: inherited_call_defs, mod_decl, tbl
              | None ->
                if m.interface then
                  let mod_decl = { mod_decl with
                    mod_decl_callables = Map.set mod_decl.mod_decl_callables ~key:func_def.func_decl.call_decl_name ~data:func_def.func_decl;
                  } in

                  let tbl = SymbolTbl.add tbl (QualIdent.from_ident func_def.func_decl.call_decl_name) (Callable func_def.func_decl) in

                  impl_callable :: inherited_call_defs, mod_decl, tbl
                else
                  Error.error (Type.to_loc tp_expr) @@ Printf.sprintf "Module %s does not implement callable %s -- incompatible with %s" (Ident.to_string mod_decl.mod_decl_name) (Ident.to_string call_name) (Type.to_string tp_expr)
              )
            )

            (* :: inherited_call_defs *)
            (* Error.error (Type.to_loc tp_expr) @@ Printf.sprintf "Module %s does not implement callable %s -- incompatible with %s" (Ident.to_string mod_decl.mod_decl_name) (Ident.to_string call_name) (Type.to_string tp_expr) *)
          | Some call_decl' -> 
            
            if (
              (* Have to use Poly.(=) because Base shadows polymorphic equality with a restricted integers-only equality. *)
              Poly.(=) call_decl'.call_decl_kind call_decl.call_decl_kind &&

              List.length call_decl'.call_decl_formals = List.length call_decl.call_decl_formals &&
              List.fold2_exn call_decl'.call_decl_formals call_decl.call_decl_formals ~init:true ~f:(fun b var1 var2 ->
                b  && (Type.equal (Map.find_exn call_decl'.call_decl_locals var1).var_type (Map.find_exn call_decl.call_decl_locals var2).var_type)
              ) &&

              List.length call_decl'.call_decl_returns = List.length call_decl.call_decl_returns &&
              List.fold2_exn call_decl'.call_decl_returns call_decl.call_decl_returns ~init:true ~f:(fun b var1 var2 ->
                b  && (Type.equal (Map.find_exn call_decl'.call_decl_locals var1).var_type (Map.find_exn call_decl.call_decl_locals var2).var_type)
              ) &&

              let alpha_renaming_map = List.fold2_exn (call_decl.call_decl_formals @ call_decl.call_decl_returns) (call_decl'.call_decl_formals @ call_decl'.call_decl_returns) ~init:(Map.empty (module QualIdent)) ~f:(fun map ident1 ident2 -> Map.add_exn map ~key:(QualIdent.from_ident ident1) ~data:(Expr.App (Var (QualIdent.from_ident ident2),  [], Expr.mk_attr (Loc.dummy) (Map.find_exn call_decl'.call_decl_locals ident2).var_type))) in

              (* Order of arguments is flipped for precond and postcond checks; first the impl_mod call_decl is passed, then the actual mod call_decl is passed. This is to match the convention of the alpha_renaming_map above. *)
              List.length call_decl.call_decl_precond = List.length call_decl'.call_decl_precond &&
              List.fold2_exn call_decl.call_decl_precond call_decl'.call_decl_precond ~init:true ~f:(fun b spec1 spec2 ->
                b  && (Expr.compare (Expr.alpha_renaming spec1.spec_form alpha_renaming_map) spec2.spec_form = 0)
              ) &&

              List.length call_decl.call_decl_postcond = List.length call_decl'.call_decl_postcond &&
              List.fold2_exn call_decl.call_decl_postcond call_decl'.call_decl_postcond ~init:true ~f:(fun b spec1 spec2 ->
                b  && (Expr.compare (Expr.alpha_renaming spec1.spec_form alpha_renaming_map) spec2.spec_form = 0)
              )
            ) 
              
            then 
              (inherited_call_defs, mod_decl, tbl)
            else
              Error.error (Type.to_loc tp_expr) @@ Printf.sprintf "Module %s implementation of callable '%s' incompatible with %s. Expected call_decl: \n%s; \n\nfound call_decl: \n%s" (Ident.to_string mod_decl.mod_decl_name) (Ident.to_string call_name) (Type.to_string tp_expr) (Util.Print.string_of_format Callable.pr_call_decl call_decl) (Util.Print.string_of_format Callable.pr_call_decl call_decl')
        ) in

        mod_decl, inherited_fields, inherited_types, inherited_vars, inherited_call_defs, tbl, (is_ra || is_ra')
      )
    ) in

    let tbl = 
      if (Ident.equal mod_decl.mod_decl_name (Ident.make "Lib" 0)) then 
        (None, snd (List.hd_exn tbl)) :: (List.tl_exn tbl)

      else 
        SymbolTbl.pop tbl 
      
    in

    let processed_members : Module.sorted_member_def_list = {
      imports = m.members.imports;
      types = type_aliases @ inherited_types;
      fields = fields @ inherited_fields;
      vars = vars @ inherited_vars;
      mod_defs = mod_defs;
      mod_aliases = mod_aliases;
      call_defs = call_defs @ inherited_call_defs; 
    } in

    let (mod_def: Module.t) =
    {
      module_decl = mod_decl;
      members = processed_members;
      interface = m.interface;
      obligations = Module.empty_sorted_member_def_list;
    } in
    
    let tbl = SymbolTbl.add tbl (QualIdent.from_ident m.module_decl.mod_decl_name) (if (Ident.equal mod_decl.mod_decl_name (Ident.make "ResourceAlgebra" 0) || does_mod_impl_ra) then (RAModDecl (mod_def, orig_mod)) else (ModDecl (mod_def, orig_mod))) in
    
    mod_def, tbl
end

let start_processing ?(tbl = SymbolTbl.push []) (m: Module.t0) = 
  let pre_processed_module = pre_process_module m in
  
  ProcessModule.process_module pre_processed_module tbl
