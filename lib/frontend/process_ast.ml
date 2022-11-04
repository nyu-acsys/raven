open Base
open Ast
open Util
open Error

(* Generic_Error is thrown by functions which don't have any Loc information. These exceptions are then meant to be caught by a caller function which can then generate the appropriate Error.erros with appropriate Loc information attached  *)

module SymbolTbl = struct
  type typing_env =
    | TypeAlias of Module.type_alias
    | Callable of Callable.call_decl
    | ModAlias of Module.module_alias
    | ModDecl of Module.module_decl
    | VarDecl of var_decl
    | Field of Module.field_def

  let typing_env_to_string t =
    match t with
    | TypeAlias tp -> "TypeAlias(" ^ Ident.to_string tp.type_alias_name ^ " --> " ^ (match tp.type_alias_def with | None -> "None" | Some tp -> (Type.to_string tp)) ^ ")"
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


 let rec fully_quantified (iden : qual_ident) tbl =
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
        | None -> fully_quantified iden ts
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

  let equal (tp_env1: t) (tp_env2: t) : bool =
    true (* ToDo: Implement properly *)
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
          mod_decl_fields = Map.add_exn mod_decl.mod_decl_fields ~key: field_def.field_name ~data: field_def
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

  let mod_decl, sorted_mems = extract_members m.mod_decl Module.empty_sorted_member_def_list (List.rev m.mod_def)  in
  {
    module_decl' = mod_decl;
    members' = sorted_mems;
    interface' = m.mod_interface;
  }

module ProcessTypeExpr = struct
  let rec process_type_expr (tp_expr: type_expr) (tbl: SymbolTbl.t) : type_expr = 
    let open Type in
    match tp_expr with
    | App ((Var qual_ident), tp_list, tp_attr) ->
      (match tp_list with
      | [] -> App ((Var (SymbolTbl.fully_quantified qual_ident tbl)), [], tp_attr)
      | _ -> raise (Generic_Error (QualIdent.to_string qual_ident ^ ": QualIdent types don't support arguments."))
      )

    | App (Set, tp_list, tp_attr) ->
      (match tp_list with
      | [tp_arg] -> let tp_arg' = process_type_expr tp_arg tbl in
        App (Set, [tp_arg'], tp_attr)
      | _ -> raise (Generic_Error "Set types take exactly one argument.")
      )

    | App (Map, tp_list, tp_attr) ->
      (match tp_list with
      | [tp1; tp2] -> let tp1 = process_type_expr tp1 tbl in
        let tp2 = process_type_expr tp2 tbl in
        App (Map, [tp1; tp2], tp_attr)
      | _ -> raise (Generic_Error "Map types take exactly two arguments")
      )

    | App (Data _variant_decl_list, _tp_list, _tp_attr) ->
      (* (match tp_list with
      | [] -> 
        let variant_decl_list = List.map variant_decl_list ~f:(fun variant_decl -> )

      | _ -> raise (Generic_Error "Data types don't take arguments")
      ) *)
      raise (Generic_Error "Data Types not presently supported")

    | App (constr, [], tp_attr) -> App (constr, [], tp_attr)

    | App (constr, _tp_list, _tp_attr) -> raise (Generic_Error (Type.to_name constr ^ " types don't take zero"))

end

let process_var_decl (var_decl: var_decl) (tbl: SymbolTbl.t) : var_decl = 
  { var_decl with
    var_type = ProcessTypeExpr.process_type_expr var_decl.var_type tbl;
  }

let does_expr_implement_type (expr: expr) (tp_expr: type_expr) : bool = 
  let tp1 = Type.join (Expr.attr_of expr).expr_type tp_expr in
  if Type.compare tp1 tp_expr = 0 then
    true 
  else 
    false

let rec process_expr (expr: expr) (tbl: SymbolTbl.t) : expr = 
  match expr with
  | App (constr, expr_list, expr_attr) ->
    (* let expr_list = List.map expr_list ~f:(fun expr -> process_expr expr tbl) in *)
    let expr_type = expr_attr.expr_type in

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
      if Type.compare (Type.meet expr_type (Type.unit)) ((Type.unit)) = 0 then
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

      | _ -> Error.lexical_error (Expr.loc expr) ((Expr.constr_to_string constr ^ " should have a Set type instead of " ^ Type.to_string expr_type ^ " or " ^ Type.to_string tp))
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
        Error.lexical_error (Expr.loc expr) ((Expr.constr_to_string constr ^ " should have a Bool type instead of " ^ Type.to_string expr_type ^ " or " ^ Type.to_string tp))
    | Bool _b, _expr_list -> Error.lexical_error (Expr.loc expr) ((Expr.constr_to_string constr ^ " takes no arguments"))
      
    | Int _num, [] ->
      let tp = Type.meet expr_type Type.int in
      if Type.compare tp Type.int = 0 then
        let expr_attr = { expr_attr with
          expr_type = Type.int;  
        } in

        App (constr, [], expr_attr)
      else
        Error.lexical_error (Expr.loc expr) ((Expr.constr_to_string constr ^ " should have a Int type instead of " ^ Type.to_string expr_type ^ " or " ^ Type.to_string tp))
    | Int _num, _expr_list -> Error.lexical_error (Expr.loc expr) ((Expr.constr_to_string constr ^ " takes no arguments"))

    | Not, [expr_arg] ->
      let expr_arg = process_expr expr_arg tbl in
      let tp = Type.meet expr_type (Expr.to_type expr_arg) in
      if Type.compare tp Type.bool = 0 then
        let expr_attr = { expr_attr with
          expr_type = Type.bool;  
        } in

        App (constr, [expr_arg], expr_attr)
      else
        Error.lexical_error (Expr.loc expr) ((Expr.to_string expr_arg ^ " should have a Bool type instead of " ^ Type.to_string (Expr.to_type expr_arg)))

    | Not, _expr_list -> Error.lexical_error (Expr.loc expr) ((Expr.constr_to_string constr ^ " takes exactly one argument"))
    
    | Uminus, [expr_arg] ->
      let expr_arg = process_expr expr_arg tbl in
      let tp = Type.meet expr_type (Expr.to_type expr_arg) in
      if Type.compare tp Type.int = 0 then
        let expr_attr = { expr_attr with
          expr_type = Type.int;  
        } in

        App (constr, [expr_arg], expr_attr)
      else
        Error.lexical_error (Expr.loc expr) ((Expr.to_string expr_arg ^ " should have Int type instead of " ^ Type.to_string (Expr.to_type expr_arg)))
    | Uminus, _expr_list -> Error.lexical_error (Expr.loc expr) ((Expr.constr_to_string constr ^ " takes exactly one argument"))

    | Eq, [expr1; expr2] ->
      let expr1 = process_expr expr1 tbl in
      let expr2 = process_expr expr2 tbl in

      let tp = Type.meet (Expr.to_type expr1) (Expr.to_type expr2) in
      if not (Type.is_any tp) then
        let expr_attr = { expr_attr with
          expr_type = Type.bool;
        } in

        App (constr, [expr1; expr2], expr_attr)
      else
        Error.lexical_error (Expr.loc expr) ((Expr.constr_to_string constr ^ " args should have same type, instead of " ^ Type.to_string (Expr.to_type expr1) ^ " and " ^ Type.to_string (Expr.to_type expr2))) 
    | Eq, _expr_list -> Error.lexical_error (Expr.loc expr) ((Expr.constr_to_string constr ^ " takes exactly two arguments"))

    | Gt, [expr1; expr2] | Lt, [expr1; expr2] | Geq, [expr1; expr2] | Leq, [expr1; expr2] ->
      let expr1 = process_expr expr1 tbl in
      let expr2 = process_expr expr2 tbl in

      let tp = Type.meet (Expr.to_type expr1) (Expr.to_type expr2) in
      if Type.compare tp Type.int = 0 then
        let expr_attr = { expr_attr with
          expr_type = Type.bool;
        } in

        App (constr, [expr1; expr2], expr_attr)
      else
        Error.lexical_error (Expr.loc expr) ((Expr.constr_to_string constr ^ " args should be of Int type, instead of " ^ Type.to_string (Expr.to_type expr1) ^ " and " ^ Type.to_string (Expr.to_type expr2))) 
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
      if Type.compare tp Type.perm = 0 || Type.compare tp Type.bool = 0  then
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

      let tp = Type.meet (Expr.to_type expr1) (Expr.to_type expr2) in
      if Type.compare tp Type.int = 0 then
        let expr_attr = { expr_attr with
          expr_type = Type.int;
        } in

        App (constr, [expr1; expr2], expr_attr)
      else
        Error.lexical_error (Expr.loc expr) ((Expr.constr_to_string constr ^ " args should be of Int type, instead of " ^ Type.to_string (Expr.to_type expr1) ^ " and " ^ Type.to_string (Expr.to_type expr2)))
    | Plus, _expr_list | Minus, _expr_list | Mult, _expr_list | Div, _expr_list | Mod, _expr_list -> Error.lexical_error (Expr.loc expr) ((Expr.constr_to_string constr ^ " takes exactly two arguments"))

    | Dot, _expr_list -> Error.lexical_error (Expr.loc expr) ("Dot expressions should not appear in the AST. Unexpected error.")

    | Call, callable_expr :: args_list ->
      let args_list = List.map args_list ~f:(fun expr -> process_expr expr tbl) in
      let callable_qual_ident = SymbolTbl.fully_quantified (ASTUtil.expr_to_qual_ident callable_expr) tbl in
      (match (SymbolTbl.find tbl callable_qual_ident) with
      | Some Callable callable_decl -> 
        let callable_arg_ident_list = callable_decl.call_decl_formals in
        let callable_arg_var_decl_list = List.map callable_arg_ident_list ~f:(fun ident -> match Map.find callable_decl.call_decl_locals ident with | Some var -> var | None -> Error.lexical_error (Expr.loc expr) ("Formal arg variable not found in CallDecl")) in
        let callable_arg_types_list = List.map callable_arg_var_decl_list ~f:(fun var_decl -> var_decl.var_type) in
        let args_type_check_list = (match List.map2 args_list callable_arg_types_list ~f:does_expr_implement_type with
            | Ok list -> list
            | Unequal_lengths -> Error.lexical_error (Expr.loc expr) (("Callable " ^ Ident.to_string callable_decl.call_decl_name ^ " called with incorrect number of arguments" ))) in
        let args_type_check = List.fold args_type_check_list ~init:true ~f:(&&) in

        if args_type_check then
          (* what type to assign to callable expressions which return multiple things? *)
          let tp = (match callable_decl.call_decl_returns with
          | [] -> Type.unit
          | [ident] -> (match Map.find callable_decl.call_decl_locals ident with
            | Some var_decl -> var_decl.var_type
            | None -> Error.lexical_error (Expr.loc expr) ("Return arg variable not found in CallDecl")
            )
          | _ -> Error.lexical_error (Expr.loc expr) ((Ident.to_string callable_decl.call_decl_name ^ ": Callables which return multiple values not presently supported"))
          ) in
          let expr_attr = { expr_attr with
            expr_type = tp;
          } in

          App (Call, callable_expr :: args_list, expr_attr)
        else
          Error.lexical_error (Expr.loc expr) ((Ident.to_string callable_decl.call_decl_name ^ ": Callable called with wrong arguments"))

      | Some tp_env -> Error.lexical_error (Expr.loc expr) ((QualIdent.to_string callable_qual_ident ^ ": expected to be a Callable instead of " ^ SymbolTbl.typing_env_to_string tp_env))
      | None -> Error.lexical_error (Expr.loc expr) ((QualIdent.to_string callable_qual_ident ^ ": not found in TypingEnv"))
      )
    | Call, [] -> Error.lexical_error (Expr.loc expr) ((Expr.constr_to_string constr ^ " needs at least one argument (the callable name)"))

    | Read, [expr1; expr2] ->
      let expr1 = process_expr expr1 tbl in
      let expr2 = process_expr expr2 tbl in

      if Type.compare (Expr.to_type expr1) (Type.ref) = 0 then
        (match SymbolTbl.find tbl (ASTUtil.expr_to_qual_ident expr2) with
        | Some (Field field_def) -> 
          let tp = field_def.field_type in
          let expr_attr = { expr_attr with
          expr_type = tp;
          } in

          App (Read, [expr1; expr2], expr_attr)

        | Some tp_env -> Error.lexical_error (Expr.loc expr) ((Expr.to_string expr2 ^ ": expected to be a Field instead of " ^ SymbolTbl.typing_env_to_string tp_env))
        | None -> Error.lexical_error (Expr.loc expr) ((Expr.to_string expr2 ^ ": not found in TypingEnv"))
         
        )

      else
        Error.lexical_error (Expr.loc expr) ((Expr.to_string expr ^ ": for Read expr, first arg should be a Ref type, instead of " ^ Type.to_string (Expr.to_type expr1)))
    | Read, _expr_list -> Error.lexical_error (Expr.loc expr) ((Expr.constr_to_string constr ^ " takes exactly two arguments"))

    | Ite, [cond_expr; if_expr; else_expr] ->
      let cond_expr = process_expr cond_expr tbl in
      let if_expr = process_expr if_expr tbl in
      let else_expr = process_expr else_expr tbl in

      if Type.compare (Expr.to_type cond_expr) Type.bool = 0 then
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
    
    | Own, [_expr1; _expr2] -> (* Implement proper type-checking for Own expressions. Do they take two args or three? *)
      expr
    | Own, _expr_list -> Error.lexical_error (Expr.loc expr) ((Expr.constr_to_string constr ^ " takes exactly two arguments"))
    
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
      let qual_ident = SymbolTbl.fully_quantified qual_ident tbl in
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

    | New tp_expr, [] -> 
      let tp_expr = ProcessTypeExpr.process_type_expr tp_expr tbl in
      let expr_attr = { expr_attr with
        expr_type = tp_expr;
      } in

      App (New tp_expr, [], expr_attr)
    
    | New _tp_expr, _expr_list -> Error.lexical_error (Expr.loc expr) ("New expressions which take arguments not presently supported")
    )

  | Binder (binder, var_decl_list, inner_expr, expr_attr) ->

    let var_decl_list = List.map var_decl_list ~f:(fun var_decl -> process_var_decl var_decl tbl) in

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

  let rec process_stmt (stmt: Stmt.t) (tbl: SymbolTbl.t) (disam_tbl: DisambiguationTbl.t) : Stmt.t * var_decl list * SymbolTbl.t * DisambiguationTbl.t = try
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
        let var_decl = process_var_decl var_def.var_decl tbl in
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

        (match assign_desc.assign_rhs with
        | App (Call, proc :: args, expr_attr) ->
          let proc_qual_ident = ASTUtil.expr_to_qual_ident proc in

          if QualIdent.compare proc_qual_ident open_au_call = 0 then
            match args with
            | [ token ] ->
              let token_expr = disambiguate_expr token disam_tbl in
              let au_token = ASTUtil.expr_to_ident token_expr
              
              in

              (match assign_desc.assign_lhs with
              | [] -> 
                let (open_au: Stmt.open_au) =
                {
                  au_token = au_token;
                  bound_vars = [];
                } in

                Basic (OpenAU open_au), [], tbl, disam_tbl
              | _ -> raise (Generic_Error ("openAU() does not take args on LHS."))
              )  

            | _ ->
                raise (Generic_Error ("openAU() called with incorrect number of arguments"))

          else if QualIdent.compare proc_qual_ident commit_au_call = 0 then
            match args with
            | token :: args -> (
                match assign_desc.assign_lhs with
                | [] ->
                    let token_expr = disambiguate_expr token disam_tbl in
                    let au_token = ASTUtil.expr_to_ident token_expr

                    in
                    let args = List.map args ~f:(fun expr -> 
                      let expr = disambiguate_expr expr disam_tbl in
                      let expr = process_expr expr tbl in
                      expr) in
                      
                    Basic (CommitAU { au_token = au_token; return_vars = args }), [], tbl, disam_tbl

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
                Basic (BindAU (ASTUtil.expr_to_ident token)), [], tbl, disam_tbl
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
                | [] -> Basic (Stmt.AbortAU (ASTUtil.expr_to_ident token)), [], tbl, disam_tbl
                | _ -> raise (Generic_Error "incorrect number of bound_args to abortAU()"))

            | _ -> raise (Generic_Error "abortAU() called without token")

          else
            let assign_lhs = List.map assign_desc.assign_lhs 
              ~f:(fun expr -> disambiguate_process_expr expr tbl disam_tbl) in

            let args = List.map args
              ~f:(fun expr -> disambiguate_expr expr disam_tbl) in

            (match (process_expr (App (Call, proc :: args, expr_attr)) tbl) with

            | App (Call, proc :: args, expr_attr) ->

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
              let expr = disambiguate_expr expr disam_tbl in
              let expr = process_expr expr tbl 
            
              in expr
          ) in

          let assign_rhs = 
            (let expr = disambiguate_expr assign_desc.assign_rhs disam_tbl in
            let expr = process_expr expr tbl 
          
            in expr
          ) in

          let (assign_desc: Stmt.assign_desc) = { 
            assign_lhs = assign_lhs;
            assign_rhs = assign_rhs;
          } in

          Basic (Assign assign_desc), [], tbl, disam_tbl
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

      (* The following constructs are not expected here because the parser stores these commands as Assign stmts. 
        The job of this function is to intercept the Assign stmts with the specific expressions on the RHS, and then transform 
        them to the appropriate construct, ie Call, New, BindAU, OpenAU, AbortAU, CommitAU etc. 
        
        This function is not expected to go over these parts of the AST again. If the following constructs are
        discovered by this function, then something unexpected has happened. *)
      | Call _call_desc -> 
        let open Stdlib.Format in
        let str = Print.string_of_format Stmt.pr_basic_stmt basic_stmt in
        raise (Generic_Error (str ^ ": InternalError: Did not expect call stmts in AST at this stage."))
      | New _new_desc ->
        let open Stdlib.Format in
        let str = Print.string_of_format Stmt.pr_basic_stmt basic_stmt in
        raise (Generic_Error (str ^ ": InternalError: Did not expect new stmts in AST at this stage."))
      | BindAU _ident ->
        let open Stdlib.Format in
        let str = Print.string_of_format Stmt.pr_basic_stmt basic_stmt in
        raise (Generic_Error (str ^ ": InternalError: Did not expect bindAU stmts in AST at this stage."))
      | OpenAU _open_au ->
        let open Stdlib.Format in
        let str = Print.string_of_format Stmt.pr_basic_stmt basic_stmt in
        raise (Generic_Error (str ^ ": InternalError: Did not expect openAU stmts in AST at this stage."))
      | AbortAU _ident ->
        let open Stdlib.Format in
        let str = Print.string_of_format Stmt.pr_basic_stmt basic_stmt in
        raise (Generic_Error (str ^ ": InternalError: Did not expect abortAU stmts in AST at this stage."))
      | CommitAU _commit_au ->
        let open Stdlib.Format in
        let str = Print.string_of_format Stmt.pr_basic_stmt basic_stmt in
        raise (Generic_Error (str ^ ": InternalError: Did not expect commitAU stmts in AST at this stage."))
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

  let process_callable ((mod_decl, tbl): Module.module_decl * SymbolTbl.t)(callable: Callable.t) : (Module.module_decl * SymbolTbl.t) * Callable.t =
    match callable with
      | FuncDef func_def ->
        (try
        let tbl = SymbolTbl.push tbl in
        let disam_tbl = (DisambiguationTbl.push []) in

        let disam_tbl, call_decl_locals_list = List.fold_map (Map.to_alist func_def.func_decl.call_decl_locals) ~init:disam_tbl ~f:(
          fun disam_tbl (_ident, var_decl) -> 
            let var_decl = process_var_decl var_decl tbl in
            let var_decl', disam_tbl = DisambiguationTbl.add_var_decl var_decl disam_tbl in
            (disam_tbl, (var_decl'.var_name, var_decl'))
        ) in
        
        let func_decl = { func_def.func_decl with
          call_decl_formals = List.map func_def.func_decl.call_decl_formals ~f:(DisambiguationTbl.find_exn disam_tbl);
          call_decl_returns = List.map func_def.func_decl.call_decl_returns ~f:(DisambiguationTbl.find_exn disam_tbl);
          call_decl_locals = Map.of_alist_exn (module Ident) call_decl_locals_list;
          call_decl_precond = List.map func_def.func_decl.call_decl_precond ~f:(process_stmt_spec tbl disam_tbl);
          call_decl_postcond = List.map func_def.func_decl.call_decl_postcond ~f:(process_stmt_spec tbl disam_tbl);
        } in 
        
        let tbl = List.fold call_decl_locals_list ~init:tbl ~f:(fun tbl (iden, var_decl) -> SymbolTbl.add tbl (QualIdent.from_ident iden) (VarDecl var_decl)) in

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
        
        let disam_tbl, call_decl_locals_list = List.fold_map (Map.to_alist proc_def.proc_decl.call_decl_locals) ~init:disam_tbl ~f:(
          fun disam_tbl (_ident, var_decl) ->
            let var_decl = process_var_decl var_decl tbl in
            let var_decl', disam_tbl = DisambiguationTbl.add_var_decl var_decl disam_tbl in
            (disam_tbl, (var_decl'.var_name, var_decl'))
        ) in

        let tbl = List.fold call_decl_locals_list ~init:tbl ~f:(fun tbl (iden, var_decl) -> SymbolTbl.add tbl (QualIdent.from_ident iden) (VarDecl var_decl)) in

        let proc_decl = { proc_def.proc_decl with
          call_decl_formals = List.map proc_def.proc_decl.call_decl_formals ~f:(DisambiguationTbl.find_exn disam_tbl);
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
          Generic_Error msg -> Error.lexical_error proc_def.proc_decl.call_decl_loc msg

  
  let rec process_callables (callables: Callable.t list) (mod_decl: Module.module_decl) (tbl: SymbolTbl.t) : Callable.t list * Module.module_decl * SymbolTbl.t =
    let (mod_decl, tbl), callables = List.fold_map callables ~init:(mod_decl, tbl) ~f:process_callable in

    callables, mod_decl, tbl
      
end


module ProcessModule = struct
  let add_imports_to_tbl (imported_mod_decl: Module.module_decl) (tbl: SymbolTbl.t) : SymbolTbl.t =
    let tbl = Map.fold (imported_mod_decl.mod_decl_fields) ~init:tbl ~f:(fun ~key:key ~data:data tbl -> SymbolTbl.add tbl (QualIdent.from_ident key) (Field data)) in

    let tbl = Map.fold (imported_mod_decl.mod_decl_mod_defs) ~init:tbl ~f:(fun ~key:key ~data:data tbl -> SymbolTbl.add tbl (QualIdent.from_ident key) (ModDecl data)) in

    let tbl = Map.fold (imported_mod_decl.mod_decl_mod_aliases) ~init:tbl ~f:(fun ~key:key ~data:data tbl -> SymbolTbl.add tbl (QualIdent.from_ident key) (ModAlias data)) in

    let tbl = Map.fold (imported_mod_decl.mod_decl_types) ~init:tbl ~f:(fun ~key:key ~data:data tbl -> SymbolTbl.add tbl (QualIdent.from_ident key) (TypeAlias data)) in

    let tbl = Map.fold (imported_mod_decl.mod_decl_callables) ~init:tbl ~f:(fun ~key:key ~data:data tbl -> SymbolTbl.add tbl (QualIdent.from_ident key) (Callable data)) in

    let tbl = Map.fold (imported_mod_decl.mod_decl_vars) ~init:tbl ~f:(fun ~key:key ~data:data tbl -> SymbolTbl.add tbl (QualIdent.from_ident key) (VarDecl data)) in

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
        | Some (ModDecl imported_mod_decl) -> 

          let mod_decl = { mod_decl with
            mod_decl_fields = Map.merge_skewed mod_decl.mod_decl_fields imported_mod_decl.mod_decl_fields ~combine:merging_function;
            mod_decl_mod_defs = Map.merge_skewed mod_decl.mod_decl_mod_defs imported_mod_decl.mod_decl_mod_defs ~combine:merging_function;
            mod_decl_mod_aliases = Map.merge_skewed mod_decl.mod_decl_mod_aliases imported_mod_decl.mod_decl_mod_aliases ~combine:merging_function;
            mod_decl_types = Map.merge_skewed mod_decl.mod_decl_types imported_mod_decl.mod_decl_types ~combine:merging_function;
            mod_decl_callables = Map.merge_skewed mod_decl.mod_decl_callables imported_mod_decl.mod_decl_callables ~combine:merging_function;
            mod_decl_vars = Map.merge_skewed mod_decl.mod_decl_vars imported_mod_decl.mod_decl_vars  ~combine:merging_function;
          } in

          let tbl = add_imports_to_tbl imported_mod_decl tbl in

          process_imports import_directives mod_decl tbl
          
        | _ -> Error.lexical_error Loc.dummy ("Import" ^ Type.to_string tp_exp ^ "could not be processed.")
        )
        
      | MemImport qual_ident ->
        match (SymbolTbl.find tbl qual_ident) with
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

        | Some (ModDecl mod_decl) -> let mod_decl = { mod_decl with
            mod_decl_mod_defs = Map.add_exn mod_decl.mod_decl_mod_defs ~key:mod_decl.mod_decl_name ~data:mod_decl;
          } in

          let tbl = SymbolTbl.add tbl (QualIdent.from_ident mod_decl.mod_decl_name) (ModDecl mod_decl) in

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
    )

  let rec process_types (type_aliases: Module.type_alias list) (mod_decl: Module.module_decl) (tbl: SymbolTbl.t) : Module.type_alias list * Module.module_decl * SymbolTbl.t = match type_aliases with 
  | [] -> [], mod_decl, tbl
  | tp_alias :: type_aliases ->
    match tp_alias.type_alias_def with
    | None -> let tbl = SymbolTbl.add tbl (QualIdent.from_ident tp_alias.type_alias_name) (TypeAlias tp_alias) in

      let (type_alias_list, mod_decl, tbl) = process_types type_aliases mod_decl tbl in

      tp_alias :: type_alias_list, mod_decl, tbl

    | Some tp_expr -> 
      let tp_expr = try 
        ProcessTypeExpr.process_type_expr tp_expr tbl 
      with (Generic_Error msg) -> Error.lexical_error tp_alias.type_alias_loc msg
      in

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
      let tp_expr = try
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
        process_var_decl var.var_decl tbl
      with (Generic_Error msg) -> Error.lexical_error var.var_decl.var_loc msg
      in

      let (var_expr: expr option) =  match var.var_init with 
      | None -> None
      | Some expr -> Some (process_expr expr tbl)

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


  let rec instantiate_module (mod_decl: Module.module_decl) (tp_args: type_expr list) (tbl: SymbolTbl.t) : Module.module_decl = 
    match (tp_args, mod_decl.mod_decl_formals) with
    | [], _ -> mod_decl
    | _tp_arg :: _, [] -> raise (Generic_Error (Ident.to_string mod_decl.mod_decl_name ^ " initialized with too many parameters"))
    | tp_arg :: tp_args, formal :: formals ->
      let formal_mod_alias = (match Map.find mod_decl.mod_decl_mod_aliases formal with 
      | None -> raise (Generic_Error "Formal arg not found; likely parser error")
      | Some mod_alias -> mod_alias) in

      if Type.is_any formal_mod_alias.mod_alias_type || does_module_implement_module (type_expr_to_mod_decl tp_arg tbl) (type_expr_to_mod_decl formal_mod_alias.mod_alias_type tbl) then
      
        let new_mod_alias = { formal_mod_alias with
          mod_alias_def = Some tp_arg;
        } in

        let mod_decl = { mod_decl with
          mod_decl_formals = formals;
          mod_decl_mod_aliases = Map.set mod_decl.mod_decl_mod_aliases ~key:formal ~data:new_mod_alias; 
        } in

        instantiate_module mod_decl tp_args tbl
      
      else
        raise (Generic_Error ("Argument " ^ Type.to_string tp_arg ^ " does not match type " ^ Type.to_string formal_mod_alias.mod_alias_type ^ " for Module " ^ Ident.to_string mod_decl.mod_decl_name))


     
  and does_module_implement_module (_mod_decl: Module.module_decl) (_implemented_mod_decl: Module.module_decl) : bool = 
    true


  and type_expr_to_mod_decl (type_expr: type_expr) (tbl: SymbolTbl.t) : Module.module_decl =
    let type_expr = ProcessTypeExpr.process_type_expr type_expr tbl in

    match type_expr with
    | App (Var qual_ident, tp_args, _tp_attr) -> 
      let tp_args = List.map ~f:(fun tp -> ProcessTypeExpr.process_type_expr tp tbl) tp_args in

      (match (SymbolTbl.find tbl qual_ident) with

      | Some (ModDecl mod_decl) -> instantiate_module mod_decl tp_args tbl

      | Some (ModAlias mod_alias) -> instantiate_module (resolve_module_alias mod_alias tbl) tp_args tbl
      
      | Some (tp_env) -> raise (Generic_Error (QualIdent.to_string qual_ident ^ ": Expected a ModAlias, found '" ^ SymbolTbl.typing_env_to_string tp_env ^ "'"))

      | None -> raise (Generic_Error (QualIdent.to_string qual_ident ^ ": not found in TypingEnv"))
      )
    | _ -> raise (Generic_Error (Type.to_string type_expr ^ " not a valid module type."))

  and resolve_module_alias (mod_alias: Module.module_alias) (tbl: SymbolTbl.t) : Module.module_decl = 
    match mod_alias.mod_alias_def with
    | None -> raise (Generic_Error ("ModAlias " ^ Ident.to_string mod_alias.mod_alias_name ^ " cannot be instantiated because it isn't defined"))
    | Some tp_expr -> type_expr_to_mod_decl tp_expr tbl


  let rec process_mod_aliases (mod_aliases: Module.module_alias list) (mod_decl: Module.module_decl) (tbl: SymbolTbl.t) : Module.module_alias list * Module.module_decl * SymbolTbl.t = 
    match mod_aliases with
    | [] -> [], mod_decl, tbl
    | mod_alias :: mod_aliases -> 
      match mod_alias.mod_alias_def with
      | None -> 
        let tbl = SymbolTbl.add tbl (QualIdent.from_ident mod_alias.mod_alias_name) (ModAlias mod_alias) in

        let (mod_aliases, mod_decl, tbl) = process_mod_aliases mod_aliases mod_decl tbl in

        (mod_alias :: mod_aliases, mod_decl, tbl)

      | Some mod_alias_def ->
        let mod_alias_def = try 
          ProcessTypeExpr.process_type_expr mod_alias_def tbl 
        with (Generic_Error str) -> Error.lexical_error mod_alias.mod_alias_loc str
        
        in

        try
          let mod_decl_of_alias = type_expr_to_mod_decl mod_alias_def tbl in

          if Type.is_any mod_alias.mod_alias_type || does_module_implement_module mod_decl_of_alias (type_expr_to_mod_decl mod_alias.mod_alias_type tbl)
            
          then

            let mod_alias = { mod_alias with
              mod_alias_def = Some mod_alias_def;
            } in

            let mod_decl = { mod_decl with
              mod_decl_mod_aliases = Map.set mod_decl.mod_decl_mod_aliases ~key:mod_alias.mod_alias_name ~data:mod_alias;
            } in
            
            let tbl = SymbolTbl.add tbl (QualIdent.from_ident mod_alias.mod_alias_name) (ModAlias mod_alias) in

            (* The following push-pop is required because we want to import the members in mod_decl_of_alias, but not in the present scope, but guarded by the mod_alias.mod_alias_name. For example, if we have:
              module M1 { module M2 = M3 },
            then we have access to M1.M2.M3_members, but not directly M1.M3_members *)
            let tbl = SymbolTbl.push_name mod_alias.mod_alias_name tbl in
            let tbl = add_imports_to_tbl mod_decl_of_alias tbl in
            let tbl = SymbolTbl.pop tbl in

            let (mod_aliases, mod_decl, tbl) = process_mod_aliases mod_aliases mod_decl tbl in

            (mod_alias :: mod_aliases, mod_decl, tbl)

          else
            Error.lexical_error mod_alias.mod_alias_loc 
            ("ModAliasDef " ^ Type.to_string mod_alias_def ^ " does not match type " ^ Type.to_string mod_alias.mod_alias_type ^ " in Module " ^ Ident.to_string mod_decl.mod_decl_name)

        with (Generic_Error str) -> Error.lexical_error mod_alias.mod_alias_loc str

  let rec process_module (m: Module.t1) (tbl: SymbolTbl.t) : Module.t * SymbolTbl.t =

    let tbl = SymbolTbl.push_name m.module_decl'.mod_decl_name tbl in

    let tbl = add_imports_to_tbl m.module_decl' tbl in

    let mod_decl, tbl = process_imports m.members'.imports' m.module_decl' tbl in

    let type_aliases, mod_decl, tbl = process_types m.members'.types' mod_decl tbl in

    let fields, mod_decl, tbl = process_fields m.members'.fields' mod_decl tbl in

    let vars, mod_decl, tbl = process_vars m.members'.vars' mod_decl tbl in

    let mod_aliases, mod_decl, tbl = process_mod_aliases m.members'.mod_aliases' mod_decl tbl in

    let call_defs, mod_decl, tbl = ProcessCallables.process_callables m.members'.call_defs' mod_decl tbl in
    
    let mod_defs, mod_decl, tbl = List.fold m.members'.mod_defs' ~init:([], mod_decl, tbl) 
    ~f:(fun (mod_defs, parent_mod_decl, tbl) (mod_def: Module.t1) -> 

      let (mod_def, tbl) = process_module mod_def tbl in

      let tbl = SymbolTbl.add tbl (QualIdent.from_ident mod_def.module_decl.mod_decl_name) (ModDecl mod_def.module_decl) in

      let (parent_mod_decl': Module.module_decl) = 
      let open Module in  
      { parent_mod_decl with
        mod_decl_mod_defs = Map.set parent_mod_decl.mod_decl_mod_defs ~key:mod_def.module_decl.mod_decl_name ~data:mod_def.module_decl;
      } in

      (mod_defs @ [mod_def], parent_mod_decl', tbl)
    )

    in

    let tbl = SymbolTbl.pop tbl in

    let processed_members : Module.processed_member_def_list = {
      imports = m.members'.imports';
      types = type_aliases;
      fields = fields;
      vars = vars;
      mod_defs = mod_defs;
      mod_aliases = mod_aliases;
      call_defs = call_defs; 
    } in

    {
      module_decl = mod_decl;
      members = processed_members;
      interface = m.interface';
      obligations = Module.empty_processed_member_def_list;
    }, tbl
end

let start_processing (m: Module.t0) = 
  let pre_processed_module = pre_process_module m in
  
  ProcessModule.process_module pre_processed_module (SymbolTbl.push [])