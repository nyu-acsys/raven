open Base
(** Checks and assigns types to all expressions *)

open Ast
open Util

module SymbolTbl = struct
  (* module IdentMap = Map.M(Ident)
     type 'a ident_map = 'a IdentMap.t *)

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

let add_var_decl (var_decl : Type.var_decl) tbl =
  SymbolTbl.add tbl (QualIdent.from_ident var_decl.var_name) (VarDecl var_decl)

let add_tp_alias (tp_alias : Module.type_alias) tbl =
  match tp_alias.type_alias_def with
  | None -> tbl
  | Some tp ->
      SymbolTbl.add tbl
        (QualIdent.from_ident tp_alias.type_alias_name)
        (TypeExpr tp)

let add_field (field : Module.field_def) tbl =
  SymbolTbl.add tbl (QualIdent.from_ident field.field_name) (Field field)

let add_callable (callable : Callable.call_decl) tbl =
  SymbolTbl.add tbl
    (QualIdent.from_ident callable.call_decl_name)
    (Callable callable)

let add_mod_alias (mod_alias : Module.module_alias) tbl =
  SymbolTbl.add tbl
    (QualIdent.from_ident mod_alias.mod_alias_name)
    (ModAlias mod_alias)

let add_mod_decl (mod_decl : Module.module_decl) tbl =
  SymbolTbl.add tbl
    (QualIdent.from_ident mod_decl.mod_decl_name)
    (ModDecl mod_decl)

let option_type_check fn arg tbl =
  match arg with
  | None -> (None, tbl)
  | Some s ->
      let s', tbl = fn s tbl in
      (Some s', tbl)

let rec list_type_check fn arg tbl =
  match arg with
  | [] -> ([], tbl)
  | l :: ls ->
      let l', tbl = fn l tbl in
      let ls', tbl = list_type_check fn ls tbl in
      (l' :: ls', tbl)

(* module IdentTypeCheck = struct
     let old_ident_type_check iden (tbl: SymbolTbl.t) = print_debug ("Old_Ident: " ^ Ident.to_string iden ^ "\n");
       match (SymbolTbl.find tbl (QualIdent.from_ident iden)) with
       | None -> raise(Failure ("Variable Not Ref: " ^ Ident.to_string iden))
       | Some id -> id.qual_base, tbl

     let new_ident_type_check iden (tbl: SymbolTbl.t) = print_debug ("New_Ident: " ^ Ident.to_string iden ^ "\n");
       let iden' = Ident.fresh iden.ident_name in
       let tbl = SymbolTbl.add tbl (QualIdent.from_ident iden) (QualIdent.from_ident iden') in
       iden', tbl

   end

   let old_ident_type_check = IdentTypeCheck.old_ident_type_check
   let new_ident_type_check = IdentTypeCheck.new_ident_type_check *)

let ident_map_type_check_add_to_tbl val_fun id_map add_fn tbl =
  let rec fn_iter l tbl =
    match l with
    | [] -> ([], tbl)
    | (id, value) :: ls ->
        let value', tbl = val_fun value tbl in
        let tbl = add_fn value' tbl in
        let ls', tbl = fn_iter ls tbl in
        ((id, value') :: ls', tbl)
  in

  let l', tbl = fn_iter (Map.to_alist id_map) tbl in
  (Map.of_alist_exn (module Ident) l', tbl)

let ident_map_add_to_tbl id_map add_fn tbl =
  let rec fn_iter l tbl =
    match l with
    | [] -> tbl
    | (_, value) :: ls ->
        let tbl = add_fn value tbl in
        let tbl = fn_iter ls tbl in
        tbl
  in

  fn_iter (Map.to_alist id_map) tbl

(* module QualIdentTypeCheck = struct
     let rec qual_ident_type_check (qual_iden : qual_ident) tbl =
       print_debug ("Old_QualIdent: " ^ QualIdent.to_string qual_iden ^ "\n");
       match (SymbolTbl.find tbl qual_iden) with
       | None -> raise(Failure ("Variable Not Ref: " ^ QualIdent.to_string qual_iden))
       | Some tp -> id, tbl
   end

   let qual_ident_type_check = QualIdentTypeCheck.qual_ident_type_check *)

module TypeTypeCheck = struct
  let rec type_attr_type_check tp_attr tbl = (tp_attr, tbl)

  and var_decl_type_check (var_decl : Type.var_decl) (tbl : SymbolTbl.t) =
    let var_tp = type_expand var_decl.var_type tbl in
    let tp, tbl =
      match SymbolTbl.find tbl (QualIdent.from_ident var_decl.var_name) with
      | None -> (var_tp, tbl)
      | Some t -> (
          match t with
          | VarDecl var -> (var.var_type, tbl)
          | _ ->
              raise
                (Failure
                   ("Variable "
                   ^ Ident.to_string var_decl.var_name
                   ^ " should have VarDecl; found: "
                   ^ SymbolTbl.typing_env_to_string t)))
      (* let var_name' = var_decl.var_name in
         let var_loc' = var_decl.var_loc in
         let var_type', tbl = var_decl.var_type, tbl in
         let var_const' = var_decl.var_const in
         let var_ghost' = var_decl.var_ghost in
         let var_implicit' = var_decl.var_implicit in

         let (var_decl' : Type.var_decl) =
         { var_name = var_name';
           var_loc = var_loc';
           var_type = var_type';
           var_const = var_const';
           var_ghost = var_ghost';
           var_implicit = var_implicit';
         }
      *)
    in

    let var_decl' = { var_decl with var_type = tp } in
    let tbl =
      SymbolTbl.add tbl
        (QualIdent.from_ident var_decl.var_name)
        (VarDecl var_decl)
    in

    (var_decl', tbl)

  and variant_decl_type_check (variant_decl : Type.variant_decl) tbl =
    let variant_name' = variant_decl.variant_name in
    (*  : ident; *)
    let variant_loc' = variant_decl.variant_loc in
    (*  : location; *)
    let variant_args', tbl =
      list_type_check var_decl_type_check variant_decl.variant_args tbl
    in

    (*  : var_decl list; *)
    let (variant_decl' : Type.variant_decl) =
      {
        variant_name = variant_name';
        variant_loc = variant_loc';
        variant_args = variant_args';
      }
    in

    (variant_decl', tbl)

  and type_expand (exp : type_expr) tbl =
    print_debug ("Type checking: " ^ Type.to_string exp ^ "\n");
    (* Resolves an App (Var _) type_expr into a built-in type. *)
    match exp with
    | App (Var qual_ident, tp_list, tp_attr) -> (
        match SymbolTbl.find tbl qual_ident with
        | None ->
            raise
              (Failure
                 ("TypeVariable "
                 ^ QualIdent.to_string qual_ident
                 ^ " not found."))
        | Some t -> (
            match t with
            | TypeExpr (App (tc'', tp_list'', _tp_attr'')) ->
                App (tc'', tp_list'' @ tp_list, tp_attr)
            | _ ->
                raise
                  (Failure
                     ("Variable "
                     ^ QualIdent.to_string qual_ident
                     ^ " should have TypeExpr."))))
    | App (tp, tp_list, tp_attr) ->
        let tp' = tp in
        let tp_list' = List.map tp_list ~f:(fun x -> type_expand x tbl) in
        let tp_attr' = tp_attr in

        App (tp', tp_list', tp_attr')
  (* | TypeData of qual_ident * type_attr
     | Dot _ -> exp (* (tp, iden, tp_attr) ->
         let tp', tbl = type_type_check tp tbl in
         let iden', tbl = old_ident_type_check iden tbl in
         let tp_attr', tbl = type_attr_type_check tp_attr tbl

       in (Dot (tp', iden', tp_attr')), tbl *) *)
end

let type_expr_expand = TypeTypeCheck.type_expand
let var_decl_type_check = TypeTypeCheck.var_decl_type_check

module ExprTypeCheck = struct
  let type_of_expr (exp : Expr.t) =
    match exp with
    | App (_, _, exp_attr) -> exp_attr.expr_type
    | Binder (_, _, _, exp_attr) -> exp_attr.expr_type

  let callable_args_check (call_decl : Callable.call_decl) args : type_expr =
    let check_call_arg_type (call_decl : Callable.call_decl) formal arg =
      let var_decl1 =
        match Map.find call_decl.call_decl_locals formal with
        | None -> raise (Failure "Internal error.")
        | Some var_decl -> var_decl
      in

      let tp1 = var_decl1.var_type in
      let tp2 = type_of_expr arg in

      if Type.compare tp1 tp2 = 0 then ()
      else
        raise
          (Failure
             ("Argument "
             ^ Ident.to_string var_decl1.var_name
             ^ " has type " ^ Type.to_string tp1 ^ "; and " ^ Expr.to_string arg
             ^ " has type " ^ Type.to_string tp2 ^ ": type mismatch"))
    in

    (match
       List.iter2
         ~f:(check_call_arg_type call_decl)
         call_decl.call_decl_formals args
     with
    | Ok () -> ()
    | Unequal_lengths ->
        raise
          (Failure
             ("CallDecl "
             ^ Ident.to_string call_decl.call_decl_name
             ^ " called with incorrect number of arguments.")));

    match call_decl.call_decl_returns with
    | [] -> Type.mk_any Loc.dummy
    | h :: _ -> (
        match Map.find call_decl.call_decl_locals h with
        | None -> raise (Failure "Internal AST error.")
        | Some var -> var.var_type)

  let rec expr_attr_type_check (expr_att : Expr.expr_attr) tbl =
    let expr_loc' = expr_att.expr_loc in
    (* : location; *)
    let expr_type', tbl = (expr_att.expr_type, tbl) in

    (* : type_expr; *)
    let (expr_att' : Expr.expr_attr) =
      { expr_loc = expr_loc'; expr_type = expr_type' }
    in

    (expr_att', tbl)

  and expr_type_check (exp : expr) tbl : expr * SymbolTbl.t =
    match exp with
    | App (Read, exp_list, exp_attr) -> (
        let exp_attr, tbl = expr_attr_type_check exp_attr tbl in
        (* x.f is stored as App(Read, [f; x], ...), ie in reverse order *)
        match exp_list with
        | [ h; t ] -> (
            let t', tbl = expr_type_check t tbl in
            match type_expr_expand (type_of_expr t') tbl with
            | App (Ref, [], _) -> (
                let qual_ident = ASTUtil.expr_to_qual_ident h in
                match SymbolTbl.find tbl qual_ident with
                | None ->
                    print_debug (SymbolTbl.to_string tbl);
                    raise
                      (Failure
                         ("TypeVariable AAA "
                         ^ QualIdent.to_string qual_ident
                         ^ " not found."))
                | Some t -> (
                    match t with
                    | Field field ->
                        ( App
                            ( Read,
                              exp_list,
                              { exp_attr with expr_type = field.field_type } ),
                          tbl )
                    | _ -> raise (Failure "Exprected type")))
            | _ ->
                raise
                  (Failure
                     ("Cannot reference the datatype "
                     ^ Type.to_string (type_of_expr t')
                     ^ "; expected a struct")))
        | _ ->
            raise (Failure "Read expression has incorrect number of arguments.")
        )
    | App (Call, exp_list, exp_attr) -> (
        let exp_attr, tbl = expr_attr_type_check exp_attr tbl in
        match exp_list with
        | head :: args -> (
            let args', tbl = list_type_check expr_type_check args tbl in
            match head with
            | App (Var callable_name, [], _) -> (
                let callable_tp = SymbolTbl.find tbl callable_name in
                match (callable_tp : SymbolTbl.typing_env option) with
                | Some (Callable call_decl) ->
                    let tp = callable_args_check call_decl args' in
                    (App (Call, exp_list, { exp_attr with expr_type = tp }), tbl)
                | _ ->
                    raise
                      (Failure
                         ("Type Error."
                         ^ QualIdent.to_string callable_name
                         ^ " should be a callable.")))
            | _ -> raise (Failure "Invalid AST state; Callable expected."))
        | _ -> raise (Failure "Invalid AST state; Call with no caller."))
    | App (con, exp_list, exp_attr) ->
        let exp_attr, tbl = expr_attr_type_check exp_attr tbl in
        let exp_list', tbl = list_type_check expr_type_check exp_list tbl in
        let exp_attr' =
          {
            exp_attr with
            expr_type =
              (match con with
              | Null | Unit -> Type.mk_any exp_attr.expr_loc
              | Bool _ -> Type.mk_bool exp_attr.expr_loc
              | Int _ -> Type.mk_int exp_attr.expr_loc
              | Empty -> Type.mk_set exp_attr.expr_loc
              | Not -> Type.mk_bool exp_attr.expr_loc
              | Uminus -> Type.mk_int exp_attr.expr_loc
              | Eq -> (
                  match exp_list' with
                  | [ h; _ ] ->
                      type_of_expr h
                      (* if (Type.compare (type_of_expr h) (type_of_expr t) = 0) then (type_of_expr h) else
                         raise (Failure("Equality expression has mismatching types.")) *)
                  | _ ->
                      raise
                        (Failure
                           "Equality expression has invalid number of arguments")
                  )
              | Gt | Lt | Geq | Leq -> Type.mk_bool exp_attr.expr_loc
              | Diff | Union | Inter | Elem | Subseteq ->
                  Type.mk_set exp_attr.expr_loc
              | And | Or | Impl -> Type.mk_bool exp_attr.expr_loc
              | Plus | Minus | Mult | Div | Mod -> Type.mk_int exp_attr.expr_loc
              (* Variable arity operators *)
              | Setenum -> Type.mk_set exp_attr.expr_loc
              | Var qual_iden -> (
                  match SymbolTbl.find tbl qual_iden with
                  | None ->
                      raise
                        (Failure
                           ("Type of `"
                           ^ QualIdent.to_string qual_iden
                           ^ "` not found."))
                  | Some t -> (
                      match t with
                      | VarDecl var -> var.var_type
                      | _ ->
                          raise
                            (Failure
                               ("Variable "
                               ^ QualIdent.to_string qual_iden
                               ^ " should have VarDecl."))))
              | New t -> t
              | Call | Read ->
                  raise (Failure "If this happens then Ocaml is broken.")
              | Dot ->
                  raise
                    (Failure
                       "Is there a Dot expr here? I thought they were dead.")
              (* Ternary operators *)
              | Ite | Write -> Type.mk_any exp_attr.expr_loc
              | Own -> Type.mk_any exp_attr.expr_loc);
          }
        in

        (App (con, exp_list', exp_attr'), tbl)
    | Binder (bind, var_decl_list, exp, exp_attr) ->
        let exp_attr, tbl = expr_attr_type_check exp_attr tbl in
        let var_decl_list', tbl =
          list_type_check var_decl_type_check var_decl_list tbl
        in
        (* var_decl_type_check adds the types of var_decls to SymbolTbl *)
        let exp', tbl = expr_type_check exp tbl in
        let exp_attr' = { exp_attr with expr_type = type_of_expr exp' } in

        (Binder (bind, var_decl_list', exp', exp_attr'), tbl)
end

let expr_type_check = ExprTypeCheck.expr_type_check
let type_of_expr = ExprTypeCheck.type_of_expr

module StmtTypeCheck = struct
  let rec spec_type_check (spec : Stmt.spec) tbl =
    let spec_form', tbl = expr_type_check spec.spec_form tbl in
    (* : expr *)
    let spec_atomic' = spec.spec_atomic in
    (* : bool *)
    let spec_name' = spec.spec_name in
    (* : string *)
    let spec_error' = spec.spec_error in

    (* : (qual_ident -> (string * string)) option *)
    let (spec' : Stmt.spec) =
      {
        spec_form = spec_form';
        spec_atomic = spec_atomic';
        spec_name = spec_name';
        spec_error = spec_error';
      }
    in

    (spec', tbl)

  and var_def_type_check (var_def : Stmt.var_def) tbl =
    let var_init', tbl =
      option_type_check expr_type_check var_def.var_init tbl
    in
    (*  : expr option; *)
    let tp =
      match var_init' with
      | None -> var_def.var_decl.var_type
      | Some e -> type_of_expr e
    in

    let var_decl' = { var_def.var_decl with var_type = tp } in
    let var_decl'', tbl = var_decl_type_check var_decl' tbl in

    (*  : var_decl; *)
    let (var_def' : Stmt.var_def) =
      { var_decl = var_decl''; var_init = var_init' }
    in

    (var_def', tbl)

  and new_desc_type_check (new_desc : Stmt.new_desc) tbl =
    let new_args', tbl =
      list_type_check expr_type_check new_desc.new_args tbl
    in
    (* : expr list; *)
    let new_lhs' = new_desc.new_lhs in
    (* : ident; *)
    let new_type' = new_desc.new_type in

    (* : type_expr; *)
    (* Todo: Need to make sure new_type' is compatible with new_args' *)
    let tbl =
      SymbolTbl.add tbl (QualIdent.from_ident new_lhs') (TypeExpr new_type')
    in

    let (new_desc' : Stmt.new_desc) =
      { new_lhs = new_lhs'; new_type = new_type'; new_args = new_args' }
    in

    (new_desc', tbl)

  and assign_desc_type_check (assign_desc : Stmt.assign_desc) tbl =
    match assign_desc.assign_lhs with
    | [ assign_lhs' ] -> (
        match assign_lhs' with
        | App (Var qual_ident, [], _) -> (
            let typed_elem = SymbolTbl.find tbl qual_ident in
            match typed_elem with
            | Some (VarDecl var_decl) ->
                if var_decl.var_const then
                  raise
                    (Failure
                       ("Const variable "
                       ^ Ident.to_string var_decl.var_name
                       ^ "("
                       ^ Loc.to_string var_decl.var_loc
                       ^ ") cannot be assigned."))
                else
                  let assign_lhs', tbl =
                    list_type_check expr_type_check assign_desc.assign_lhs tbl
                  in
                  (*  : expr list; *)
                  let assign_rhs', tbl =
                    expr_type_check assign_desc.assign_rhs tbl
                  in

                  (*  : expr; *)
                  let (assign_desc' : Stmt.assign_desc) =
                    { assign_lhs = assign_lhs'; assign_rhs = assign_rhs' }
                  in

                  (assign_desc', tbl)
            | Some x ->
                raise
                  (Failure
                     ("Expected "
                     ^ SymbolTbl.typing_env_to_string x
                     ^ " to be a callable."))
            | _ ->
                raise (Failure ("Could not find " ^ Expr.to_string assign_lhs'))
            )
        | App (Read, _var :: _args, _) ->
            let assign_lhs', tbl =
              list_type_check expr_type_check assign_desc.assign_lhs tbl
            in
            (*  : expr list; *)
            let assign_rhs', tbl = expr_type_check assign_desc.assign_rhs tbl in

            (*  : expr; *)
            let (assign_desc' : Stmt.assign_desc) =
              { assign_lhs = assign_lhs'; assign_rhs = assign_rhs' }
            in

            (assign_desc', tbl)
        | _ ->
            raise (Failure "Error with assign stmt")
            (* Todo: Figure out what to do with this, unify etc. *))
    | _ -> raise (Failure "Error, Assign has |lhs| != 1")

  and call_desc_type_check (call_desc : Stmt.call_desc) (tbl : SymbolTbl.t) =
    let typed_elem = SymbolTbl.find tbl call_desc.call_name in
    match typed_elem with
    | Some (Callable call_decl) ->
        if
          (* Todo: also check types of args and returns *)
          List.length call_desc.call_lhs
          = List.length call_decl.call_decl_returns
          && List.length call_desc.call_args
             = List.length call_decl.call_decl_formals
        then
          (* let call_lhs', tbl = (* list_type_check qual_ident_type_check *) call_desc.call_lhs, tbl in (*  : qual_ident list; *)
               let call_name', tbl = (* qual_ident_type_check *) call_desc.call_name, tbl in (*  : qual_ident; *)
               let call_args', tbl = list_type_check expr_type_check call_desc.call_args tbl in (*  : expr list; *)

               let (call_desc': Stmt.call_desc) =
               { call_lhs = call_lhs';
                 call_name = call_name';
                 call_args = call_args';
               }

             in call_desc', tbl *)
          (call_desc, tbl)
        else raise (Failure "Error")
    | Some x ->
        raise
          (Failure
             ("Expected "
             ^ SymbolTbl.typing_env_to_string x
             ^ " to be a callable."))
    | _ ->
        raise
          (Failure ("Could not find " ^ QualIdent.to_string call_desc.call_name))

  and fold_desc_type_check (fold_desc : Stmt.fold_desc) tbl =
    let fold_expr', tbl = expr_type_check fold_desc.fold_expr tbl in

    (* : expr; *)
    let (fold_desc' : Stmt.fold_desc) = { fold_expr = fold_expr' } in

    (fold_desc', tbl)

  and unfold_desc_type_check (unfold_desc : Stmt.unfold_desc) tbl =
    let unfold_expr', tbl = expr_type_check unfold_desc.unfold_expr tbl in

    let (unfold_desc' : Stmt.unfold_desc) = { unfold_expr = unfold_expr' } in

    (unfold_desc', tbl)

  and basic_stmt_desc_type_check (basic_stmt : Stmt.basic_stmt_desc) tbl :
      Stmt.basic_stmt_desc * SymbolTbl.t =
    match basic_stmt with
    | VarDef var_def ->
        let var_def', tbl = var_def_type_check var_def tbl in
        (VarDef var_def', tbl)
    | Assume spec ->
        let spec', tbl = spec_type_check spec tbl in
        (Assume spec', tbl)
    | Assert spec ->
        let spec', tbl = spec_type_check spec tbl in
        (Assert spec', tbl)
    | New new_desc ->
        let new_desc', tbl = new_desc_type_check new_desc tbl in
        (New new_desc', tbl)
    | Assign assign_desc ->
        let assign_desc', tbl = assign_desc_type_check assign_desc tbl in
        (Assign assign_desc', tbl)
    | Havoc expr_list ->
        let expr_list', tbl = list_type_check expr_type_check expr_list tbl in
        (Havoc expr_list', tbl)
    | Call call_desc ->
        let call_desc', tbl = call_desc_type_check call_desc tbl in
        (Call call_desc', tbl)
    | Return expr_list ->
        let expr_list', tbl = list_type_check expr_type_check expr_list tbl in
        (Return expr_list', tbl)
    | Fold fold_desc ->
        let fold_desc', tbl = fold_desc_type_check fold_desc tbl in
        (Fold fold_desc', tbl)
    | Unfold unfold_desc ->
        let unfold_desc', tbl = unfold_desc_type_check unfold_desc tbl in
        (Unfold unfold_desc', tbl)
    | x -> (x, tbl)

  and stmt_type_check (stmt : Stmt.t) tbl =
    let stmt_desc', tbl = stmt_desc_type_check stmt.stmt_desc tbl in
    (*  stmt_desc; *)
    let stmt_loc' = stmt.stmt_loc in

    (*  location; *)
    let (stmt' : Stmt.t) = { stmt_desc = stmt_desc'; stmt_loc = stmt_loc' } in

    (stmt', tbl)

  and loop_desc_type_check (loop_desc : Stmt.loop_desc)
      tbl (* : SymbolTbl.t * var_decl list *) =
    let tbl = SymbolTbl.push tbl in
    let loop_contract', tbl =
      list_type_check spec_type_check loop_desc.loop_contract tbl
    in
    (* : spec list; *)
    let loop_prebody', tbl = stmt_type_check loop_desc.loop_prebody tbl in
    (* : t; *)
    let loop_test', tbl = expr_type_check loop_desc.loop_test tbl in
    (* : expr; *)
    let loop_postbody', tbl = stmt_type_check loop_desc.loop_postbody tbl in
    (* : t; *)
    let tbl = SymbolTbl.pop tbl in

    let (loop_desc' : Stmt.loop_desc) =
      {
        loop_contract = loop_contract';
        loop_prebody = loop_prebody';
        loop_test = loop_test';
        loop_postbody = loop_postbody';
      }
    in

    (loop_desc', tbl)

  and cond_desc_type_check (cond_desc : Stmt.cond_desc) tbl =
    let cond_test', tbl = expr_type_check cond_desc.cond_test tbl in
    (* : expr; *)
    let tbl = SymbolTbl.push tbl in
    let cond_then', tbl = stmt_type_check cond_desc.cond_then tbl in
    (* : t; *)
    let tbl = SymbolTbl.pop tbl in
    let tbl = SymbolTbl.push tbl in
    let cond_else', tbl = stmt_type_check cond_desc.cond_else tbl in
    (* : t; *)
    let tbl = SymbolTbl.pop tbl in

    let (cond_desc' : Stmt.cond_desc) =
      { cond_test = cond_test'; cond_then = cond_then'; cond_else = cond_else' }
    in

    (cond_desc', tbl)

  and ghost_desc_type_check (ghost_desc : Stmt.ghost_desc) tbl =
    let tbl = SymbolTbl.push tbl in
    let ghost_body', tbl =
      list_type_check stmt_type_check ghost_desc.ghost_body tbl
    in
    (* : t list; *)
    let tbl = SymbolTbl.pop tbl in

    let (ghost_desc' : Stmt.ghost_desc) = { ghost_body = ghost_body' } in

    (ghost_desc', tbl)

  and stmt_desc_type_check stmt_desc tbl =
    match stmt_desc with
    | Block stmt_list ->
        let tbl = SymbolTbl.push tbl in
        let stmt_list', tbl = list_type_check stmt_type_check stmt_list tbl in
        let tbl = SymbolTbl.pop tbl in
        (Block stmt_list', tbl)
    | Basic basic_stmt_desc ->
        let basic_stmt_desc', tbl =
          basic_stmt_desc_type_check basic_stmt_desc tbl
        in
        (Basic basic_stmt_desc', tbl)
    | Loop loop_desc ->
        let loop_desc', tbl = loop_desc_type_check loop_desc tbl in
        (Loop loop_desc', tbl)
    | Cond cond_desc ->
        let cond_desc', tbl = cond_desc_type_check cond_desc tbl in
        (Cond cond_desc', tbl)
    | Ghost ghost_desc ->
        let ghost_desc', tbl = ghost_desc_type_check ghost_desc tbl in
        (Ghost ghost_desc', tbl)
end

let stmt_type_check = StmtTypeCheck.stmt_type_check

module CallableTypeCheck = struct
  let rec locals_to_string (m : (ident * Type.var_decl) list) =
    match m with
    | [] -> ""
    | l :: ls ->
        Ident.to_string (fst l)
        ^ " -> "
        ^ Type.to_string (snd l).var_type
        ^ ",   " ^ locals_to_string ls

  let rec call_decl_type_check (call_decl : Callable.call_decl) tbl =
    let call_decl_kind' = call_decl.call_decl_kind in
    (* Todo: Figure out how to store callable types *)
    let call_decl_name', tbl = (call_decl.call_decl_name, tbl) in
    let tbl = SymbolTbl.push tbl in
    (* Corresponding SymbolTbl.pop made in proc_def_type_check and func_def_type_check *)
    let call_decl_locals', tbl =
      ident_map_type_check_add_to_tbl var_decl_type_check
        call_decl.call_decl_locals add_var_decl tbl
    in

    (* print_debug ("LOCALS: " ^ (locals_to_string (Map.to_alist call_decl_locals')) ^ "\n"); *)
    let call_decl_formals', tbl = (call_decl.call_decl_formals, tbl) in
    let call_decl_returns', tbl = (call_decl.call_decl_returns, tbl) in
    let call_decl_precond', tbl =
      list_type_check StmtTypeCheck.spec_type_check call_decl.call_decl_precond
        tbl
    in
    let call_decl_postcond', tbl =
      list_type_check StmtTypeCheck.spec_type_check call_decl.call_decl_postcond
        tbl
    in
    let call_decl_loc' = call_decl.call_decl_loc in

    let (call_decl' : Callable.call_decl) =
      {
        call_decl_kind = call_decl_kind';
        call_decl_name = call_decl_name';
        call_decl_formals = call_decl_formals';
        call_decl_returns = call_decl_returns';
        call_decl_locals = call_decl_locals';
        call_decl_precond = call_decl_precond';
        call_decl_postcond = call_decl_postcond';
        call_decl_loc = call_decl_loc';
      }
    in

    let tbl =
      match tbl with
      | [] -> []
      | h :: t ->
          h
          ::
          (match call_decl_kind' with
          | Proc (* -> add_callable call_decl' t *)
          | Pred | Func | Lemma (* -> add_callable call_decl' t *)
          | Invariant ->
              add_callable call_decl' t)
    in

    (call_decl', tbl)

  and proc_def_type_check (proc_def : Callable.proc_def) tbl =
    let proc_decl', tbl = call_decl_type_check proc_def.proc_decl tbl in
    let proc_body', tbl =
      option_type_check stmt_type_check proc_def.proc_body tbl
    in

    let tbl = SymbolTbl.pop tbl in

    (* Corresponding push made in call_decl_type_check *)
    let (proc_def' : Callable.proc_def) =
      { proc_decl = proc_decl'; proc_body = proc_body' }
    in

    (proc_def', tbl)

  and func_def_type_check (func_def : Callable.func_def) tbl =
    let func_decl', tbl = call_decl_type_check func_def.func_decl tbl in
    let func_body', tbl =
      option_type_check expr_type_check func_def.func_body tbl
    in
    let tbl = SymbolTbl.pop tbl in

    (* Corresponding push made in call_decl_type_check *)
    let (func_def' : Callable.func_def) =
      { func_decl = func_decl'; func_body = func_body' }
    in

    (func_def', tbl)

  and callable_type_check (call : Callable.t) tbl : Callable.t * SymbolTbl.t =
    match call with
    | FuncDef func_def ->
        let func_def', tbl = func_def_type_check func_def tbl in
        (FuncDef func_def', tbl)
    | ProcDef proc_def ->
        let proc_def', tbl = proc_def_type_check proc_def tbl in
        (ProcDef proc_def', tbl)
end

let callable_type_check = CallableTypeCheck.callable_type_check

module ModuleTypeCheck = struct
  let rec type_alias_type_check (type_alias : Module.type_alias) tbl =
    let type_alias_name', tbl = (type_alias.type_alias_name, tbl) in
    let type_alias_def', tbl = (type_alias.type_alias_def, tbl) in
    let type_alias_rep' = type_alias.type_alias_rep in
    let type_alias_loc' = type_alias.type_alias_loc in

    let (type_alias' : Module.type_alias) =
      {
        type_alias_name = type_alias_name';
        type_alias_def = type_alias_def';
        type_alias_rep = type_alias_rep';
        type_alias_loc = type_alias_loc';
      }
    in

    let tbl = add_tp_alias type_alias' tbl in

    (type_alias', tbl)

  and field_type_check (field : Module.field_def) tbl =
    let field_name', tbl = (field.field_name, tbl) in
    let field_type', tbl = (field.field_type, tbl) in

    let (field' : Module.field_def) =
      { field_name = field_name'; field_type = field_type' }
    in

    let tbl = add_field field' tbl in

    (field', tbl)

  and mod_alias_type_check (mod_alias : Module.module_alias) tbl =
    let mod_alias_name', tbl = (mod_alias.mod_alias_name, tbl) in
    let mod_alias_type', tbl = (mod_alias.mod_alias_type, tbl) in
    let mod_alias_def', tbl = (mod_alias.mod_alias_def, tbl) in
    let mod_alias_loc' = mod_alias.mod_alias_loc in

    let (mod_alias' : Module.module_alias) =
      {
        mod_alias_name = mod_alias_name';
        mod_alias_type = mod_alias_type';
        mod_alias_def = mod_alias_def';
        mod_alias_loc = mod_alias_loc';
      }
    in

    let tbl = add_mod_alias mod_alias' tbl in

    (mod_alias', tbl)

  and mod_decl_type_check (mod_decl : Module.module_decl) tbl =
    (* Might try pushing and popping in table here instead of in module_type_check *)
    let mod_decl_name', tbl = (mod_decl.mod_decl_name, tbl) in
    let mod_decl_formals', tbl = (mod_decl.mod_decl_formals, tbl) in
    let mod_decl_returns', tbl = (mod_decl.mod_decl_returns, tbl) in
    let mod_decl_fields', tbl = (mod_decl.mod_decl_fields, tbl) in
    let mod_decl_rep', tbl = (mod_decl.mod_decl_rep, tbl) in
    let mod_decl_mod_defs', tbl =
      ident_map_type_check_add_to_tbl mod_decl_type_check
        mod_decl.mod_decl_mod_defs add_mod_decl tbl
    in
    let mod_decl_mod_aliases', tbl =
      ident_map_type_check_add_to_tbl mod_alias_type_check
        mod_decl.mod_decl_mod_aliases add_mod_alias tbl
    in
    let mod_decl_types', tbl =
      ident_map_type_check_add_to_tbl type_alias_type_check
        mod_decl.mod_decl_types add_tp_alias tbl
    in
    let mod_decl_callables', tbl =
      ident_map_type_check_add_to_tbl CallableTypeCheck.call_decl_type_check
        mod_decl.mod_decl_callables add_callable tbl
    in
    let mod_decl_vars', tbl =
      ident_map_type_check_add_to_tbl var_decl_type_check mod_decl.mod_decl_vars
        add_var_decl tbl
    in
    let mod_decl_loc' = mod_decl.mod_decl_loc in

    let (mod_decl' : Module.module_decl) =
      {
        mod_decl_name = mod_decl_name';
        mod_decl_formals = mod_decl_formals';
        mod_decl_returns = mod_decl_returns';
        mod_decl_fields = mod_decl_fields';
        mod_decl_rep = mod_decl_rep';
        mod_decl_mod_defs = mod_decl_mod_defs';
        mod_decl_mod_aliases = mod_decl_mod_aliases';
        mod_decl_types = mod_decl_types';
        mod_decl_callables = mod_decl_callables';
        mod_decl_vars = mod_decl_vars';
        mod_decl_loc = mod_decl_loc';
      }
    in

    (mod_decl', tbl)

  and import_directive_type_check (imp_dir : Module.import_directive) tbl :
      Module.import_directive * SymbolTbl.t =
    match imp_dir with
    | ModImport tp_exp ->
        let tp_exp', tbl = (tp_exp, tbl) in
        (ModImport tp_exp', tbl)
    | MemImport qual_id ->
        let qual_id', tbl = (qual_id, tbl) in
        (MemImport qual_id', tbl)

  and member_def_type_check (mem_def : Module.member_def) tbl :
      Module.member_def * SymbolTbl.t =
    match mem_def with
    | TypeAlias tp_alias ->
        let tp_alias', tbl = type_alias_type_check tp_alias tbl in
        (TypeAlias tp_alias', tbl)
    | Import imp_dir ->
        let imp_dir', tbl = import_directive_type_check imp_dir tbl in
        (Import imp_dir', tbl)
    | ModDef mod_def ->
        let mod_def', tbl = mod_def_type_check mod_def tbl in
        (ModDef mod_def', tbl)
    | FieldDef field ->
        let field', tbl = field_type_check field tbl in
        (FieldDef field', tbl (* TODO: Refine *))
    | ValDef var_defn ->
        let var_defn', tbl = StmtTypeCheck.var_def_type_check var_defn tbl in
        (ValDef var_defn', tbl)
    | CallDef call ->
        let call', tbl = callable_type_check call tbl in
        (* let tbl = (match call' with
           | FuncDef fn -> add_callable fn.func_decl tbl
           | ProcDef pc -> add_callable pc.proc_decl tbl)

           in *)
        (* Adding callables to the tbl is done in CallableTypeCheck.call_decl_type_check *)
        (CallDef call', tbl)

  and mod_def_type_check mod_def tbl =
    match mod_def with
    | ModImpl mod1 ->
        let mod', tbl = module_type_check mod1 tbl in
        let tbl = add_mod_decl mod1.mod_decl tbl in
        (ModImpl mod', tbl)
    | ModAlias mod_alias ->
        let mod_alias', tbl = mod_alias_type_check mod_alias tbl in
        let tbl = add_mod_alias mod_alias tbl in
        (ModAlias mod_alias', tbl)

  and module_type_check mod1 tbl =
    let rec extract_members (mod_defs_list : Module.member_def list)
        (rep, fields, mod_defs, mod_aliases, types, callables, vars) =
      match mod_defs_list with
      | [] -> (rep, fields, mod_defs, mod_aliases, types, callables, vars)
      | def :: defs -> (
          match def with
          | TypeAlias type_alias ->
              let rep =
                if type_alias.type_alias_rep then
                  Some type_alias.type_alias_name
                else rep
              in
              let types =
                Map.add_exn types ~key:type_alias.type_alias_name
                  ~data:type_alias
              in
              extract_members defs
                (rep, fields, mod_defs, mod_aliases, types, callables, vars)
          | Import _ ->
              extract_members defs
                (rep, fields, mod_defs, mod_aliases, types, callables, vars)
          | ModDef module_def -> (
              match module_def with
              | ModImpl mod_impl ->
                  let mod_defs =
                    Map.add_exn mod_defs ~key:mod_impl.mod_decl.mod_decl_name
                      ~data:mod_impl.mod_decl
                  in
                  extract_members defs
                    (rep, fields, mod_defs, mod_aliases, types, callables, vars)
              | ModAlias mod_alias ->
                  let mod_aliases =
                    Map.add_exn mod_aliases ~key:mod_alias.mod_alias_name
                      ~data:mod_alias
                  in
                  extract_members defs
                    (rep, fields, mod_defs, mod_aliases, types, callables, vars)
              )
          | FieldDef field ->
              let fields =
                Map.add_exn fields ~key:field.field_name ~data:field.field_type
              in
              extract_members defs
                (rep, fields, mod_defs, mod_aliases, types, callables, vars)
          | ValDef v ->
              let vars =
                Map.add_exn vars ~key:v.var_decl.var_name ~data:v.var_decl
              in
              extract_members defs
                (rep, fields, mod_defs, mod_aliases, types, callables, vars)
          | CallDef call ->
              let cl_decl =
                match call with
                | FuncDef fn -> fn.func_decl
                | ProcDef proc -> proc.proc_decl
              in

              let callables =
                Map.add_exn callables ~key:cl_decl.call_decl_name ~data:cl_decl
              in
              extract_members defs
                (rep, fields, mod_defs, mod_aliases, types, callables, vars))
    in

    let mod_decl_name' = mod1.mod_decl.mod_decl_name in

    let tbl = SymbolTbl.push_name mod_decl_name' tbl in
    let mod_def', tbl =
      list_type_check member_def_type_check mod1.mod_def tbl
    in
    let rep, fields, mod_defs, mod_aliases, types, callables, vars =
      extract_members mod_def'
        ( mod1.mod_decl.mod_decl_rep,
          mod1.mod_decl.mod_decl_fields,
          mod1.mod_decl.mod_decl_mod_defs,
          mod1.mod_decl.mod_decl_mod_aliases,
          mod1.mod_decl.mod_decl_types,
          mod1.mod_decl.mod_decl_callables,
          mod1.mod_decl.mod_decl_vars )
    in

    let (mod_decl' : Module.module_decl) =
      {
        mod_decl_name = mod_decl_name';
        mod_decl_formals = mod1.mod_decl.mod_decl_formals;
        mod_decl_returns = mod1.mod_decl.mod_decl_returns;
        mod_decl_rep = rep;
        mod_decl_fields = fields;
        mod_decl_mod_defs = mod_defs;
        mod_decl_mod_aliases = mod_aliases;
        mod_decl_types = types;
        mod_decl_callables = callables;
        mod_decl_vars = vars;
        mod_decl_loc = mod1.mod_decl.mod_decl_loc;
      }
    in

    (*
       let tbl = ident_map_add_to_tbl mod_defs add_mod_decl tbl in
       let tbl = ident_map_add_to_tbl mod_aliases add_mod_alias tbl in
       let tbl = ident_map_add_to_tbl types add_tp_alias tbl in
       let tbl = ident_map_add_to_tbl callables add_callable tbl in
    *)
    let mod_interface' = mod1.mod_interface in
    let tbl = SymbolTbl.pop tbl in

    let (mod' : Module.t) =
      {
        mod_decl = mod_decl';
        mod_def = mod_def';
        mod_interface = mod_interface';
      }
    in

    (mod', tbl)
  (* let tbl = SymbolTbl.push_name mod1.mod_decl.mod_decl_name tbl in

       let mod_decl', tbl = mod_decl_type_check mod1.mod_decl tbl in
       print_debug ("\027[32mHERE: " ^ Ident.to_string mod_decl'.mod_decl_name ^ "\027[0m");
       let mod_def', tbl = list_type_check member_def_type_check mod1.mod_def tbl in

       let mod_interface' = mod1.mod_interface in

       let tbl = SymbolTbl.pop tbl in

       let (mod': Module.t) =
       { mod_decl = mod_decl';
         mod_def = mod_def';
         mod_interface = mod_interface';
       }

     in mod', tbl *)
end

let module_type_check = ModuleTypeCheck.module_type_check
let start_type_check m = module_type_check m (SymbolTbl.push [])
