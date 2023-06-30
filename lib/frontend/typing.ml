open Base
open Ast
open Util
open Error

let type_mismatch_error loc exp_ty fnd_ty =
  Error.type_error loc
    (Printf.sprintf !"Expected an expression of type\n  %{Type}\nbut found an expression of type\n  %{Type}" exp_ty fnd_ty)

let arguments_to_string d =
  if d = 1 then "one argument" else Printf.sprintf "%d arguments" d

let tuple_arg_mismatch_error loc expected =
  Error.type_error loc (Printf.sprintf "Expected tuple with %s components." (arguments_to_string expected))

let module_arg_mismatch_error loc typ_constr expected =
  Error.type_error loc (Printf.sprintf "Module %s expects %s." (Type.to_name typ_constr) (arguments_to_string expected))

let unexpected_functor_error loc =
  Error.type_error loc ("A functor cannot be instantiated in this context.")
    
module ProcessTypeExpr = struct
  let rec process_type_expr (tp_expr: type_expr) : type_expr Rewriter.t =
    let open Type in
    let open Rewriter.Syntax in
    let loc = Type.loc tp_expr in
    match tp_expr with
    | App ((Var qual_ident), [], tp_attr) ->
      let+ fully_qualified_qual_ident, symbol = Rewriter.resolve_and_find loc qual_ident in
      begin match Rewriter.Symbol.orig_symbol symbol with
        | TypeDef _tp_alias -> App ((Var fully_qualified_qual_ident), [], tp_attr)
        | ModDef m ->
          begin match m.mod_decl.mod_decl_rep with
            | None ->
              Logs.debug (fun mm -> mm "%a" Ident.pr m.mod_decl.mod_decl_name);
              Error.type_error tp_attr.type_loc
                ("Module " ^ QualIdent.to_string qual_ident ^ " does not have a rep type. It cannot be used in a context expecting a type.")
                
            | Some rep_ident ->
              let rep_fully_qualified_qual_ident = QualIdent.append fully_qualified_qual_ident rep_ident in
              App (Var rep_fully_qualified_qual_ident, [], tp_attr)
          end
        | ModInst _ ->
          unexpected_functor_error tp_attr.type_loc 
        | _ -> 
          Error.type_error tp_attr.type_loc ("Expected type identifier.")
      end
      
    | App (Var _, _, tp_attr) ->
      unexpected_functor_error tp_attr.type_loc 
  
    | App (Set, tp_list, tp_attr) ->
      (match tp_list with
       | [tp_arg] ->
         let+ tp_arg' = process_type_expr tp_arg in
         App (Set, [tp_arg'], tp_attr)
      | _ -> module_arg_mismatch_error (Type.to_loc tp_expr) Set 1
      )

    | App (Map, tp_list, tp_attr) ->
      (match tp_list with
       | [tp1; tp2] ->
         let+ tp1 = process_type_expr tp1
         and+ tp2 = process_type_expr tp2 in
         App (Map, [tp1; tp2], tp_attr)
      | _ -> module_arg_mismatch_error (Type.to_loc tp_expr) Map 2
      )

    | App (Data _variant_decl_list, _tp_list, _tp_attr) ->
      (* The parser should prevent this from happening. *)
      Error.internal_error (Type.loc tp_expr) "Data types can only be defined as new types, not used inline."

    | App (Prod, tp_list, tp_attr) ->
      let+ tp_list = Rewriter.List.map tp_list ~f:process_type_expr in
      App (Prod, tp_list, tp_attr)

    | App (constr, [], tp_attr) ->
      Rewriter.return @@ App (constr, [], tp_attr)

    | App (constr, _tp_list, _tp_attr) ->
      (* The parser should prevent this from happening. *)
      Error.internal_error (Type.loc tp_expr) (Type.to_name constr ^ " types don't take arguments")


  let rec expand_type_expr (tp_expr: type_expr) : Type.t Rewriter.t = 
    let open Rewriter.Syntax in
    match tp_expr with
    | App (constr, tp_expr_list, tp_attr) ->
      match constr with
      | Var qual_iden ->
        (* Var types with args not supported. Polymorphic types need to be instantiated as separate modules before using. *)
        let* qual_ident, symbol = Rewriter.resolve_and_find (Type.to_loc tp_expr) qual_iden in
        let* qual_ident_def = Rewriter.Symbol.reify_type_def (Type.loc tp_expr) symbol in
        begin match qual_ident_def with
          | None -> Rewriter.return @@ Type.App (Var qual_ident, tp_expr_list, tp_attr)
          | Some tp_expr -> expand_type_expr tp_expr
        end
      | _ ->
        let+ expanded_tp_expr_list = Rewriter.List.map tp_expr_list ~f:expand_type_expr in
        Type.App (constr, expanded_tp_expr_list, tp_attr)
    


  let process_var_decl (var_decl: var_decl) : var_decl Rewriter.t = 
    let open Rewriter.Syntax in
    if (not (Type.equal var_decl.var_type (Type.any)))
    then
      let+ var_type = process_type_expr var_decl.var_type in
      { var_decl with var_type }
    else
      Error.error (var_decl.var_loc) @@ Printf.sprintf "Type annotation missing for variable '%s'" (Ident.to_string var_decl.var_name)

end

(* TODO: move this function inside of process_expr *)
let check_and_set (expr: expr) (given_typ_lb: type_expr) (given_typ_ub: type_expr) (expected_typ: type_expr) : expr Rewriter.t = 
  let open Rewriter.Syntax in
  let+ given_typ_lb = 
    try
      ProcessTypeExpr.expand_type_expr given_typ_lb
    with
    | Msg(lbl, _loc, msg) -> Error.fail ?lbl (Expr.loc expr) msg
  and+ given_typ_ub = ProcessTypeExpr.expand_type_expr given_typ_ub
  and+ expected_typ = ProcessTypeExpr.expand_type_expr expected_typ in
  let typ = Type.meet given_typ_ub expected_typ in
  if Type.subtype_of given_typ_lb typ then
    Expr.set_type expr typ
  else
    type_mismatch_error (Expr.loc expr) expected_typ given_typ_ub

(** Infer and check type of [expr] subject to typing environment [tbl] and expected type [expected_typ] *)
let rec process_expr (expr: expr) (expected_typ: type_expr) : expr Rewriter.t =
  let open Rewriter.Syntax in
  match expr with
  | App (constr, expr_list, expr_attr) ->
    begin match constr, expr_list with
    (* Constants *)
    | (Null | Real _ | Int _ | Bool _ | Empty), [] ->
        let given_type_lb, given_type_ub =
          match constr with
          | Null -> Type.ref, Type.ref
          | Real _ -> Type.real, Type.real
          | Int _ -> Type.int, Type.int
          | Bool _ -> Type.bool, Type.bool
          | Empty -> Type.(mk_set (Expr.loc expr) bot), Type.(mk_set (Expr.loc expr) any)
          | _ -> assert false
        in
        check_and_set expr given_type_lb given_type_ub expected_typ
    | (Null | Real _ | Int _ | Bool _ | Empty), _expr_list ->
        Error.type_error (Expr.loc expr) ((Expr.constr_to_string constr ^ " takes no arguments"))

    (* Variables *)
    | Var qual_ident, [] ->
      let* qual_ident, symbol = 
        Rewriter.resolve_and_find (Expr.loc expr) qual_ident
      in
      let* symbol = Rewriter.Symbol.reify symbol in
      let given_typ =
        match symbol with
        | VarDef var_def ->
          var_def.var_decl.var_type     
        | FieldDef field_def -> 
          field_def.field_type
        | _ -> Error.type_error (Expr.loc expr) "Expected variable or field identifier."
      in
      let expr = Expr.App (Var qual_ident, [], expr_attr) in
      check_and_set expr given_typ given_typ expected_typ
    | Var _qual_ident, _expr_list -> Error.type_error (Expr.loc expr) (("variable or field identifiers take no arguments"))

          
    (* Unary expressions *)
    | (Not | Uminus), [expr_arg] ->
        let given_type_ub =
          match constr with
          | Uminus -> Type.num
          | Not -> Type.bool
          | _ -> assert false
        in
        let* expr_arg = process_expr expr_arg given_type_ub in
        let given_type_lb = Expr.to_type expr_arg in
        check_and_set (App (constr, [expr_arg], expr_attr)) given_type_lb given_type_ub expected_typ
    | (Not | Uminus), _expr_list ->
        Error.type_error (Expr.loc expr) ((Expr.constr_to_string constr ^ " takes exactly one argument"))

    (* Binary expressions *)
    | (MapLookUp
      | Diff | Union | Inter
      | Plus | Minus | Mult | Div | Mod
      | Gt | Lt | Geq | Leq
      | And | Or | Impl
      | Subseteq | Elem | Eq), [expr1; expr2] ->
        (* infer and propagated expected type of expr1 *)
        let expected_typ1 =
          match constr with
          | MapLookUp -> Type.(map bot expected_typ)
          | Diff | Union | Inter ->
              Type.meet expected_typ Type.(set_typed any)
          | Subseteq -> Type.(set_typed any)
          | Plus | Minus | Mult | Div | Mod | Gt | Lt | Geq | Leq -> Type.num
          | And | Or -> Type.perm
          | Impl -> Type.bool (* antecedent must be pure *)
          | Elem | Eq -> Type.any
          | _ -> assert false
        in
        let* expr1 = process_expr expr1 expected_typ1 in
        let typ1 = Expr.to_type expr1 in
        (* infer and propagated expected type of expr2 *)
        let expected_typ2 =
          match constr with
          | MapLookUp -> Type.map_dom typ1
          | Diff | Union | Inter 
          | Plus | Minus | Mult | Div | Mod
          | Subseteq | Eq | Gt | Lt | Geq | Leq -> typ1
          | And | Or | Impl -> Type.perm
          | Elem -> Type.(set_typed typ1)
          | _ -> assert false
        in
        let* expr2 = process_expr expr2 expected_typ2 in
        let typ2 = Expr.to_type expr2 in
        
        (* backpropagate typ2 to expr1 if needed *)
        let expected_typ1 =
          match constr with
          | MapLookUp -> Type.(map typ2 (Type.map_codom typ1))
          | Diff | Union | Inter
          | Plus | Minus | Mult | Div | Mod
          | Subseteq | Eq | Gt | Lt | Geq | Leq -> typ2
          | And | Or | Impl -> Type.perm
          | Elem -> Type.set_elem typ2
          | _ -> assert false
        in
        let* expr1 =
          if Type.equal expected_typ1 typ1
          then Rewriter.return expr1
          else process_expr expr1 expected_typ1
        in

        let expected_typ =
          if not @@ Type.is_any expected_typ then expected_typ else
          match constr with
          | MapLookUp -> Type.map_codom typ1
          | Diff | Union | Inter
          | Plus | Minus | Mult | Div | Mod -> typ2
          | And | Or | Impl -> Type.perm
          | Subseteq | Eq | Gt | Lt | Geq | Leq
          | Elem -> Type.bool
          | _ -> assert false
        in
        
        (* recompute expr and check against its expected type *)
        let given_typ_lb, given_typ_ub =
          match constr with
          | MapLookUp ->
              let typ = expr1 |> Expr.to_type |> Type.map_codom in
              typ, typ
          | Diff | Union | Inter ->
              Type.(set_typed bot), Type.(set_typed any)
          | Plus | Minus | Mult | Div | Mod ->
              let typ = expr1 |> Expr.to_type in
              typ, typ
          | And | Or | Impl ->
              let typ = expr1 |> Expr.to_type in
            Type.bool, Type.join typ typ2
          | Subseteq | Elem | Eq | Gt | Lt | Geq | Leq ->
              Type.bool, Type.bool
          | _ -> assert false
        in         
        check_and_set (App (constr, [expr1; expr2], expr_attr)) given_typ_lb given_typ_ub expected_typ
          
    | (MapLookUp | Diff | Union | Inter | Plus | Minus | Mult | Div | Mod | And | Or | Impl | Subseteq | Elem | Eq | Gt | Lt | Geq | Leq), _expr_list ->
        Error.type_error (Expr.loc expr) ((Expr.constr_to_string constr ^ " takes exactly two arguments"))

    (* Ternary expressions *)
    | (Ite | MapUpdate), [expr1; expr2; expr3] ->
        (* infer and propagate expected type of expr1 *)
        let expected_typ1 =
          match constr with
          | Ite -> Type.bool
          | MapUpdate -> Type.(map bot any)
          | _ -> assert false
        in
        let* expr1 = process_expr expr1 expected_typ1 in
        let typ1 = Expr.to_type expr1 in
        (* infer and propagate expected type of expr2 *)
        let expected_typ2 =
          match constr with
          | Ite -> expected_typ
          | MapUpdate -> Type.map_dom typ1
          | _ -> assert false
        in
        let* expr2 = process_expr expr2 expected_typ2 in
        let typ2 = Expr.to_type expr2 in
        (* infer and propagate expected type of expr3 *)
        let expected_typ3 =
          match constr with
          | Ite -> expected_typ2
          | MapUpdate -> Type.map_codom typ2
          | _ -> assert false
        in
        let* expr3 = process_expr expr3 expected_typ3 in
        let typ3 = Expr.to_type expr3 in
        (* backpropagate typ3 to expr2 if needed *)
        let expected_typ2 =
          match constr with
          | Ite -> typ3
          | MapUpdate -> typ2
          | _ -> assert false
        in
        let* expr2 =
          if Type.equal expected_typ2 typ2
          then Rewriter.return expr2
          else process_expr expr2 expected_typ2
        in
        let typ2 = Expr.to_type expr2 in
        (* backpropagate typ3 and typ2 to expr1 if needed *)
        let expected_typ1 =
          match constr with
          | Ite -> Type.bool
          | MapUpdate -> Type.map typ2 typ3
          | _ -> assert false
        in
        let* expr1 =
          if Type.equal expected_typ1 typ1 
          then Rewriter.return expr1
          else process_expr expr1 expected_typ1
        in
        let typ1 = Expr.to_type expr1 in
        (* recompute expr and check against its expected type *)
        let given_typ_lb, given_typ_ub =
          match constr with
          | Ite -> typ3, typ3
          | MapUpdate -> typ1, typ1
          | _ -> assert false
        in
        let expr = Expr.App (constr, [expr1; expr2; expr3], expr_attr) in
        check_and_set expr given_typ_lb given_typ_ub expected_typ

    | (Ite | MapUpdate), _expr_list -> Error.type_error (Expr.loc expr) ((Expr.constr_to_string constr ^ " takes exactly three arguments"))

    (* Ownership predicates *)
    | Own, expr1 :: expr2 :: expr3 :: expr4_opt ->
        let* expr1 = process_expr expr1 Type.ref in
        let field_type = match Expr.to_type expr1 with
          | App (Fld, [tp_expr], _) -> tp_expr
          | _ -> Error.type_error (Expr.loc expr2) "Expected field identifier."
        in
        let* expr2 = process_expr expr2 field_type
        and* expr3 = process_expr expr3 field_type
        (* Implicitely case-split on heap RA vs. other RA *)
        and* expr4_opt = Rewriter.List.map expr4_opt ~f:(fun e -> process_expr e Type.real) in
        (* Reconstruct and check expr *)
        let expr = Expr.App (Own, expr1 :: expr2 :: expr3 :: expr4_opt, expr_attr) in
        check_and_set expr Type.perm Type.perm expected_typ

    | Own, _expr_list -> Error.type_error (Expr.loc expr) ((Expr.constr_to_string constr ^ " takes either three or four arguments"))

    (* Data constructor expressions *)
    | DataConstr (constr_ident, loc), args_list ->
      let* constr_decl =
        let* symbol = Rewriter.find loc constr_ident in
        let+ symbol = Rewriter.Symbol.reify symbol in
        match symbol with
        | ConstrDef constr -> constr
        | _ -> Error.type_error loc "Expected data constructor"
      in
      let constr_arg_types_list = List.map constr_decl.constr_args ~f:(fun var_decl -> var_decl.var_type) in
      let* maybe_args_list = Rewriter.List.map2 args_list constr_arg_types_list ~f:(fun expr tp_expr -> process_expr expr tp_expr) in
      let args_list =
        match maybe_args_list with
        | Ok list -> list
        | Unequal_lengths ->
            Error.type_error (Expr.loc expr) (("data constructor " ^ QualIdent.to_string constr_ident ^ " called with incorrect number of arguments" ))
      in
      let given_typ = constr_decl.constr_return_type in
      let expr = Expr.App (constr, args_list, expr_attr) in
      check_and_set expr given_typ given_typ expected_typ

    (* Data destructor expressions *)
    | DataDestr (destr_qual_ident, loc), [expr1]  -> 
      let* destr =
        let* symbol = Rewriter.find loc destr_qual_ident in
        let+ symbol = Rewriter.Symbol.reify symbol in
        match symbol with    
        | DestrDef destr -> destr
        | _tp_env -> Error.type_error loc "Expected data destructor"
      in
      let* expr1 = process_expr expr1 destr.destr_arg in
      let given_typ = destr.destr_return_type in
      let expr = Expr.App (constr, [expr1], expr_attr) in
      check_and_set expr given_typ given_typ expected_typ

    | DataDestr _, _ -> Error.type_error (Expr.loc expr) ((Expr.constr_to_string constr ^ " takes exactly one argument"))

    (* Call expressions *)
    | Call (callable_qual_ident, loc), args_list ->
      let* callable_qual_ident, symbol = Rewriter.resolve_and_find (Expr.loc expr) callable_qual_ident in
      let* symbol = Rewriter.Symbol.reify symbol in
      begin match symbol with
      | ConstrDef _constr ->
          process_expr (App (DataConstr (callable_qual_ident, loc), args_list, Expr.attr_of expr)) expected_typ
      | CallDef callable ->
        let callable_decl = Callable.to_decl callable in
        let* args_list = process_callable_args (Expr.loc expr) callable_decl args_list in
        let given_typ = Callable.return_type callable_decl in
        let expr = Expr.App (Call (callable_qual_ident, loc), args_list, expr_attr) in
        check_and_set expr given_typ given_typ expected_typ
      | _ -> Error.type_error (Expr.loc expr) ("Expected a callable identifier, but found " ^ QualIdent.to_string callable_qual_ident)
      end

    (* Read expressions *)
    | Read, [expr1; App (Var qual_ident, [], expr_attr) as expr2] ->
      let* qual_ident, symbol = 
          Rewriter.resolve_and_find (Expr.loc expr) qual_ident
      in
      let* symbol = Rewriter.Symbol.reify symbol in
      begin match symbol with
      | DestrDef _ ->
          process_expr (App (DataDestr (qual_ident, Expr.loc expr2), [expr1], expr_attr)) expected_typ
      | FieldDef field_def -> 
        let* expr1 = process_expr expr1 Type.ref in
        let given_typ = field_def.field_type in
        let expr2 = Expr.App (Var qual_ident, [], expr_attr) in
        let expr2 = Expr.set_type expr2 given_typ in
        let expr = Expr.App (Read, [expr1; expr2], expr_attr) in
        check_and_set expr given_typ given_typ expected_typ
      | _ -> Error.type_error (Expr.loc expr) ("Expected field or destructor identifier, but found " ^ QualIdent.to_string qual_ident)
      end

    | Read, _expr_list -> Error.type_error (Expr.loc expr) ((Expr.constr_to_string constr ^ " takes exactly two arguments"))

    (* Set enumeration expressions *)
    | Setenum, [] -> process_expr (App (Empty, [], expr_attr)) expected_typ 
          
    | Setenum, member_expr_list ->
        (* TODO: make type inference for member_expr_list more precise by using expected_typ *)
        let* member_expr_list, elem_typ =
          Rewriter.List.fold_right member_expr_list
            ~f:(fun mexpr (member_expr_list, elem_typ) ->
              let+ mexpr = process_expr mexpr elem_typ in
               (mexpr :: member_expr_list, Expr.to_type mexpr))
            ~init:([], Type.any)
        in
        let given_typ = Type.set_typed elem_typ in
        let expr = Expr.App (Setenum, member_expr_list, expr_attr) in
        check_and_set expr given_typ given_typ expected_typ

    (* Tuple expressions *)
    | Tuple, elem_expr_list ->
      let typed_elem_expr_list =
        match expected_typ with
        | App (Prod, ts, _) ->
          List.zip elem_expr_list ts |> (function
              | Ok res -> res
              | _ -> tuple_arg_mismatch_error (Expr.loc expr) (List.length ts))
        | _ -> List.map ~f:(fun e -> (e, Type.any)) elem_expr_list 
      in
      let* elem_expr_list, elem_types =
        Rewriter.List.fold_right typed_elem_expr_list
          ~f:(fun (mexpr, mtyp) (elem_expr_list, elem_types) ->
              let+ mexpr = process_expr mexpr mtyp in
              (mexpr :: elem_expr_list, Expr.to_type mexpr :: elem_types))
          ~init:([], [])
      in
      let given_typ = Type.mk_prod (Expr.loc expr) elem_types in
      let expr = Expr.App (Tuple, elem_expr_list, expr_attr) in
      check_and_set expr given_typ given_typ expected_typ
          
  end

  | Binder (binder, var_decl_list, inner_expr, expr_attr) ->
    let* var_decl_list =
      Rewriter.List.map var_decl_list
        ~f:(fun var_decl -> ProcessTypeExpr.process_var_decl var_decl)
    and* _ = Rewriter.add_locals var_decl_list in

    match binder with
    | Forall | Exists ->
      let* inner_expr = process_expr inner_expr Type.perm in
      let expr = Expr.Binder (binder, var_decl_list, inner_expr, expr_attr) in
      check_and_set expr Type.bool Type.perm expected_typ

    | Compr ->
      let var_decl = 
        match var_decl_list with
        | [v] -> v
        | _ -> Error.type_error (Expr.loc expr) "Map/Set compr only take one quantified variable"
      in
      let* inner_expr = process_expr inner_expr Type.any in
      let inner_expr_type = Expr.to_type inner_expr in

      let expr_typ = 
        if Type.equal inner_expr_type Type.bool then
          Type.mk_set var_decl.var_loc var_decl.var_type
        else
          Type.mk_map var_decl.var_loc var_decl.var_type inner_expr_type

      in

      let expr = Expr.Binder (binder, var_decl_list, inner_expr, expr_attr) in
      check_and_set expr expr_typ expr_typ expected_typ

  (* end of process_expr *)

  and process_callable_args loc callable_decl args_list =
    let callable_formals = callable_decl.call_decl_formals in

    (* Check if too few arguments given. *)
    let _ =
      List.drop callable_formals (List.length args_list) |>
      List.exists ~f:(fun var_decl -> not @@ var_decl.Type.var_implicit) |>
      fun b -> if b then
        Error.type_error loc @@
          Printf.sprintf "Some explicit arguments are missing in this call to %s" (Ident.to_string callable_decl.call_decl_name)
    in

    let provided_formals =
      List.take callable_formals (List.length args_list)
    in
    let explicit_formal_types = List.map provided_formals ~f:(fun var_decl -> (*ProcessTypeExpr.process_type_expr*) var_decl.Type.var_type) in
    let open Rewriter.Syntax in
    match%bind Rewriter.List.map2 args_list explicit_formal_types ~f:(fun expr tp_expr -> process_expr expr tp_expr) with
    | Ok args_list -> Rewriter.return args_list
    | Unequal_lengths -> 
      (* Catches if too many args given. *)
      Error.type_error loc @@
      Printf.sprintf "Too many arguments passed to %s" (Ident.to_string callable_decl.call_decl_name)


module ProcessCallable = struct
  module DisambiguationTbl = struct
    type t = (ident ident_map) list  
    let push (disam_tbl: t) : t = Map.empty (module Ident) :: disam_tbl
    let pop (disam_tbl: t) : t = match disam_tbl with
      | _ :: disam_tbl -> disam_tbl
      | [] -> raise (Invalid_argument "Empty DisambiguationTbl")

    let add (disam_tbl: t) loc name new_name : t = match disam_tbl with
      | hd :: tl ->
        begin match Map.add hd ~key:name ~data:new_name with
          | `Ok hd -> hd :: tl
          | `Duplicate -> Error.redeclaration_error loc (Ident.to_string name)
        end
      | [] -> raise (Invalid_argument "Empty DisambiguationTbl")

    let rec find (disam_tbl: t) name =
      match disam_tbl with
      | [] -> None
      | map :: ts -> (
          match Map.find map name with | None -> find ts name | Some id -> Some id
        )

    let rec find_exn (disam_tbl: t) name =
      match disam_tbl with
      | map :: ts ->
        begin match Map.find map name with
          | None -> find_exn ts name
          | Some id -> id
        end
      | [] -> raise Stdlib.Not_found

    let add_var_decl (var_decl: Type.var_decl) (disam_tbl: t) : Type.var_decl * t = 
      let new_name = Ident.fresh var_decl.var_name.ident_name in
      let disam_tbl = add disam_tbl var_decl.var_loc var_decl.var_name new_name in
      let var_decl =
        { var_decl with
          var_name = new_name;
        }
      in

      var_decl, disam_tbl
  end

  let disambiguate_ident (qual_ident: qual_ident) (disam_tbl: DisambiguationTbl.t) =
    if List.is_empty qual_ident.qual_path then
      let base =
        match DisambiguationTbl.find disam_tbl qual_ident.qual_base with
        | Some iden -> iden
        | None -> qual_ident.qual_base;
      in
      QualIdent.make [] base
    else
      qual_ident

  let rec disambiguate_expr (expr: expr) (disam_tbl: DisambiguationTbl.t) : expr = 
    match expr with
    | App (constr, expr_list, expr_attr) -> 
      let expr_list = List.map expr_list ~f:(fun expr -> disambiguate_expr expr disam_tbl) in
      
      let constr = match constr with
      | Var qual_ident -> 
        let qual_ident = disambiguate_ident qual_ident disam_tbl in
        Expr.Var qual_ident
      | DataConstr (qual_ident, loc) ->
        let qual_ident = disambiguate_ident qual_ident disam_tbl in
        Expr.DataConstr (qual_ident, loc)
      | DataDestr (qual_ident, loc) ->
        let qual_ident = disambiguate_ident qual_ident disam_tbl in
        Expr.DataDestr (qual_ident, loc)
      | Call (qual_ident, loc) ->
        let qual_ident = disambiguate_ident qual_ident disam_tbl in
        Expr.Call (qual_ident, loc)
      | _ -> constr
      in
      App (constr, expr_list, expr_attr)
      
    | Binder (binder, var_decl_list, expr, expr_attr) -> 
      Binder (binder, var_decl_list, disambiguate_expr expr disam_tbl, expr_attr)

  let disambiguate_process_expr (expr: expr) (expected_typ: type_expr) (disam_tbl: DisambiguationTbl.t) : expr Rewriter.t = 
    let expr = disambiguate_expr expr disam_tbl in
    process_expr expr expected_typ
          

  let process_stmt_spec (disam_tbl: DisambiguationTbl.t) (spec: Stmt.spec) : Stmt.spec Rewriter.t =
    let open Rewriter.Syntax in
    let+ spec_form = disambiguate_process_expr spec.spec_form Type.perm disam_tbl in
    { spec with spec_form }



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
    
  (*
  let rec pre_process_stmt (stmt: Stmt.t) : Stmt.t list Rewriter.t = 
    (* This function only takes stmts of type:
        var x : Type = val;
        
        and unfolds them into:
        var x : Type;
        x := val;
    *)
    match stmt.stmt_desc with
    | Block block_desc ->
      let+ stmt_list =
        Rewriter.List.fold_right block_desc.block_body ~init:[]
          ~f:(fun stmt stmt_list ->
              let+ stmts = pre_process_stmt stmt in
              stmts @ stmt_list)
      in
      [{stmt with stmt_desc = Block { block_desc with block_body = stmt_list } }]
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
        | stmt_list ->
          {loop_desc.loop_prebody with stmt_desc = Block { block_body = stmt_list; block_is_ghost = false } }
      ) in

      let loop_postbody_list = pre_process_stmt loop_desc.loop_postbody in
      let loop_postbody' = (match loop_postbody_list with
        | [stmt'] -> stmt'
        | stmt_list -> 
          {loop_desc.loop_postbody with stmt_desc = Stmt.mk_block stmt_list }
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
        | stmt_list -> {stmt_desc = Stmt.mk_block stmt_list; stmt_loc = cond_desc.cond_then.stmt_loc;}
      ) in

      let cond_else_list = pre_process_stmt cond_desc.cond_else in
      let cond_else' = (match cond_else_list with
        | [stmt'] -> stmt'
        | stmt_list -> {stmt_desc = Stmt.mk_block stmt_list; stmt_loc = cond_desc.cond_else.stmt_loc;}
      ) in

      let cond_desc' = { cond_desc with
            cond_then = cond_then';
            cond_else = cond_else';
      } in

      [{stmt with stmt_desc = Cond cond_desc';}]
    )
  *)
  let process_stmt ?(new_scope=true) (expected_return_type: Type.t) (stmt: Stmt.t) (disam_tbl: DisambiguationTbl.t) : (Stmt.t * var_decl list * DisambiguationTbl.t) Rewriter.t =
    let rec process_stmt ?(new_scope=true) stmt disam_tbl =
    let open Rewriter.Syntax in
    (*let stmt_list = pre_process_stmt stmt in
    let stmt = match stmt_list with
      | [stmt'] -> stmt'
      | stmt_list -> {stmt_desc = Block { block_body = stmt_list; block_is_ghost = false }; stmt_loc = stmt.stmt_loc;}
    in*)

    let+ stmt_desc, locals, disam_tbl =
    match stmt.Stmt.stmt_desc with
    | Block block_desc ->
      let disam_tbl =
        if new_scope then
          DisambiguationTbl.push disam_tbl
        else disam_tbl
      in

      let+ (locals, disam_tbl), stmt_list = Rewriter.List.fold_map block_desc.block_body ~init:([], disam_tbl) 
        ~f:(fun (locals, disam_tbl) stmt -> 
             let+ stmt, locals', disam_tbl = process_stmt stmt disam_tbl in
             (locals @ locals', disam_tbl), stmt
           )
      in

      let disam_tbl =
        if new_scope
        then DisambiguationTbl.pop disam_tbl
        else disam_tbl
      in
      
      Stmt.Block { block_desc with block_body = stmt_list }, locals, disam_tbl

    | Basic basic_stmt ->
      begin match basic_stmt with
      | VarDef var_def -> 
        let* var_decl = ProcessTypeExpr.process_var_decl var_def.var_decl in
        let var_decl, disam_tbl' = DisambiguationTbl.add_var_decl var_decl disam_tbl in
        let+ stmt =
          let var = QualIdent.from_ident var_decl.var_name in
          match var_def.var_init with
          | None -> Rewriter.return @@ Stmt.Basic (Havoc var)
          | Some expr ->
            let+ expr = disambiguate_process_expr expr var_decl.var_type disam_tbl in
            let var_expr = Expr.App (Var var, [], {expr_loc = stmt.stmt_loc; expr_type = var_decl.var_type}) in
            let assign_desc = Stmt.{ assign_lhs = [var_expr]; assign_rhs = expr } in
            Stmt.Basic (Assign assign_desc)
        and+ _ = Rewriter.add_locals [var_decl] in
        stmt, [var_decl], disam_tbl'
      | Spec (sk, spec) -> 
        let+ spec = process_stmt_spec disam_tbl spec in
        Stmt.Basic (Spec (sk, spec)), [], disam_tbl

      | Assign assign_desc ->
        (* THIS IS WHERE the RHS needs to be examined; *)

        (let open_au_call = QualIdent.from_ident (Ident.make "openAU" 0) in
        let commit_au_call = QualIdent.from_ident (Ident.make "commitAU" 0) in
        let bind_au_call = QualIdent.from_ident (Ident.make "bindAU" 0) in
        let abort_au_call = QualIdent.from_ident (Ident.make "abortAU" 0) in
        let fpu_call = QualIdent.from_ident (Ident.make "fpu" 0) in

        begin match assign_desc.assign_rhs with
        | App (Call (proc_qual_ident, proc_loc), args, expr_attr) ->
          (* TODO: there is a lot of duplicated code below that can be factored out.
             Also, add comments that indicate which kind of assignment statement is handled in each case
           *)
          if QualIdent.(proc_qual_ident = open_au_call) then
            match args with
            | [ token ] ->
              let+ token_expr = disambiguate_process_expr token Type.any (* TODO: make expected type more precise *) disam_tbl in
              let au_token = Expr.to_ident token_expr in

              begin match assign_desc.assign_lhs with
              | [] -> 
                let open_au = au_token in

                Stmt.Basic (OpenAU open_au), [], disam_tbl
              | _ -> Error.type_error stmt.stmt_loc ("openAU does not take arguments")
              end

            | _ ->
                Error.error (Stmt.loc stmt) ("openAU() called with incorrect number of arguments")

          else if QualIdent.(proc_qual_ident = commit_au_call) then
            match args with
            | token :: [] -> (
                match assign_desc.assign_lhs with
                | [] ->
                    let+ token_expr = disambiguate_process_expr token Type.any (* TODO: make expected type more precise *) disam_tbl in
                    let au_token = Expr.to_ident token_expr in
                      
                    Stmt.Basic (CommitAU au_token), [], disam_tbl

                | _ ->
                    Error.error (Stmt.loc stmt) ("incorrect number of LHS args to commitAU()")
                )
            | _ ->
                Error.error (Stmt.loc stmt) ("commitAU() called with incorrect number of arguments")

          else if QualIdent.(proc_qual_ident = bind_au_call) then
            match args with
            | [] -> 
              (match assign_desc.assign_lhs with
              | [ token ] ->
                let+ token_expr = disambiguate_process_expr token Type.any (* TODO: make expected type more precise *) disam_tbl in
                Stmt.Basic (BindAU (Expr.to_ident token_expr)), [], disam_tbl
              | _ ->
                Error.error (Stmt.loc stmt) ("incorrect number of bound_args to bindAU()")
              )

            | _ ->
              Error.error (Stmt.loc stmt) ("bindAU() called with incorrect number of arguments")

          else if QualIdent.(proc_qual_ident = abort_au_call) then
            match args with
            | [ token ] -> (
                match assign_desc.assign_lhs with
                | [] -> 
                  let+ token_expr = disambiguate_process_expr token Type.any (* TODO: make expected type more precise *) disam_tbl in
                  Stmt.Basic (Stmt.AbortAU (Expr.to_ident token_expr)), [], disam_tbl
                | _ ->
                  Error.error (Stmt.loc stmt) "incorrect number of bound_args to abortAU()")
            | _ -> Error.error (Stmt.loc stmt)  "abortAU() called without token"

          else if QualIdent.(proc_qual_ident = fpu_call) then
            match assign_desc.assign_lhs, args with
            | [], [ref_expr; field_expr; val_expr] -> 
                let* ref_expr = disambiguate_process_expr ref_expr Type.ref disam_tbl
                and* field_expr = disambiguate_process_expr field_expr Type.any disam_tbl in
                let field_type = match Expr.to_type field_expr with
                  | App (Fld, [tp_expr], _) -> tp_expr
                  | _ -> Error.type_error (Expr.loc field_expr) "Expected field identifier."
                in
                let+ val_expr = disambiguate_process_expr val_expr field_type disam_tbl in
                let field_qual_ident = Expr.to_qual_ident field_expr in
                let fpu_desc = {
                  Stmt.fpu_ref = ref_expr;
                  fpu_field = field_qual_ident;
                  fpu_val = val_expr;
                } in
                Stmt.Basic (Stmt.Fpu fpu_desc), [], disam_tbl
            | _ ->
              Error.error (Stmt.loc stmt) "fpu() called incorrectly"

          else
            let* assign_lhs = Rewriter.List.map assign_desc.assign_lhs 
                ~f:(fun expr -> disambiguate_process_expr expr Type.any disam_tbl)
            in

            let expected_return_type =
              List.map assign_lhs ~f:Expr.to_type |> function
              | [] -> Type.unit
              | [t] -> t
              | ts -> Type.mk_prod proc_loc ts
            in
            
            let+ call_expr = 
              Expr.App (Call (proc_qual_ident, proc_loc), args, expr_attr) |>
              fun expr -> disambiguate_process_expr expr expected_return_type disam_tbl (* TODO: <- replace this with the expected type *)
            in

            begin match call_expr with

            | App (Call (proc_qual_ident, _), args, _expr_attr) ->

              let (call_desc : Stmt.call_desc) =
                {
                  call_lhs =
                    List.map assign_lhs ~f:Expr.to_qual_ident;
                  call_name = proc_qual_ident;
                  call_args = args;
                }
              in

              Stmt.Basic (Call call_desc), [] , disam_tbl

            | _ -> failwith "Unexpected error during type checking."
            end

        | _ ->
          let* assign_lhs = Rewriter.List.map assign_desc.assign_lhs 
            ~f:(fun expr -> 
                 disambiguate_process_expr expr Type.any disam_tbl)
          in

          let expected_type =
            List.map assign_lhs ~f:Expr.to_type |> function
            | [] -> Type.unit
            | [t] -> t
            | ts -> Type.mk_prod stmt.stmt_loc ts
          in

          let+ assign_rhs = 
            disambiguate_process_expr assign_desc.assign_rhs expected_type disam_tbl
          in
              
          let assign_desc =
            Stmt.{ 
              assign_lhs = assign_lhs;
              assign_rhs = assign_rhs;
            }
          in
          
          Stmt.Basic (Assign assign_desc), [], disam_tbl
        end
        )
      
      | Havoc qual_ident ->
        let qual_ident = disambiguate_ident qual_ident disam_tbl in
        Rewriter.return (Stmt.Basic (Havoc qual_ident), [], disam_tbl)

      | Return expr ->
        let+ expr =
          disambiguate_process_expr expr expected_return_type disam_tbl
        in
        Stmt.Basic (Return expr), [], disam_tbl

      | Use use_desc ->

        let* use_name, symbol = 
          let id = disambiguate_ident use_desc.use_name disam_tbl in
          Rewriter.resolve_and_find stmt.stmt_loc id
        in
        let* symbol = Rewriter.Symbol.reify symbol in
        
        let pred_decl =
          match symbol, use_desc.use_kind with
          | CallDef { call_decl = ({call_decl_kind = Pred; _} as pred_decl); _ }, (Fold | Unfold) -> pred_decl
          | CallDef { call_decl = ({call_decl_kind = Invariant; _} as pred_decl); _ }, (OpenInv | CloseInv) -> pred_decl
          | _, (Fold | Unfold) ->
            Error.type_error stmt.stmt_loc ("Expected predicate identifier, but found " ^ QualIdent.to_string use_name)
          | _ ->
            Error.type_error stmt.stmt_loc ("Expected invariant identifier, but found " ^ QualIdent.to_string use_name)
        in
        
        let use_args =
          List.map use_desc.use_args ~f:(fun expr -> disambiguate_expr expr disam_tbl)
        in

        let+ use_args = process_callable_args stmt.stmt_loc pred_decl use_args in

        Stmt.Basic (Use {use_desc with use_name = use_name; use_args = use_args}), [], disam_tbl
      
      | New new_desc ->
        let new_qual_ident = disambiguate_ident new_desc.new_lhs disam_tbl in
        let* new_qual_ident, symbol = Rewriter.resolve_and_find stmt.stmt_loc new_qual_ident in
        let* symbol = Rewriter.Symbol.reify symbol in
        let var_decl = 
          match symbol with
          | VarDef var_def -> var_def.var_decl
          | _ -> Error.type_error stmt.stmt_loc "Expected variable identifier on left-hand side of new"
        in
        let* var_type_expanded = ProcessTypeExpr.expand_type_expr var_decl.var_type in
        
        if Type.equal var_type_expanded Type.ref then
          let process_field_init (field_name, expr_opt) =
            let* field_name, symbol = Rewriter.resolve_and_find stmt.stmt_loc field_name in
            let* field_type = Rewriter.Symbol.reify_field_type stmt.stmt_loc symbol in
            let+ expr_opt = Rewriter.map_opt expr_opt (fun expr -> disambiguate_process_expr expr field_type disam_tbl) in
            (field_name, expr_opt)
          in
          let+ new_args = Rewriter.List.map new_desc.new_args ~f:process_field_init in

          let new_desc = 
            Stmt.{
              new_lhs = new_qual_ident;
              new_args;
            }
          in

          Stmt.Basic (New new_desc), [], disam_tbl
        else
          type_mismatch_error stmt.stmt_loc Type.ref var_decl.var_type
        
        

      (* The following constructs are not expected here because the parser stores these commands as Assign stmts. 
        The job of this function is to intercept the Assign stmts with the specific expressions on the RHS, and then transform 
        them to the appropriate construct, ie Call, New, BindAU, OpenAU, AbortAU, CommitAU etc. 
        
        This function is not expected to go over these parts of the AST again. If the following constructs are
        discovered by this function, then something unexpected has happened. *)
      | Call _call_desc -> 
        internal_error (Stmt.loc stmt) "Did not expect call stmts in AST at this stage."
      | BindAU _ident ->
        internal_error (Stmt.loc stmt) "Did not expect bindAU stmts in AST at this stage."
      | OpenAU _open_au ->
        internal_error (Stmt.loc stmt) "Did not expect openAU stmts in AST at this stage."
      | AbortAU _ident ->
        internal_error (Stmt.loc stmt) "Did not expect abortAU stmts in AST at this stage."
      | CommitAU _commit_au ->
        internal_error (Stmt.loc stmt) "Did not expect commitAU stmts in AST at this stage."
      | Fpu _fpu_desc -> 
        internal_error (Stmt.loc stmt) "Did not expect Fpu stmts in AST at this stage."
    end
    | Loop loop_desc -> 
      let* loop_contract = Rewriter.List.map loop_desc.loop_contract ~f:(process_stmt_spec disam_tbl) in

      let disam_tbl = DisambiguationTbl.push disam_tbl in
      let* loop_prebody, locals', disam_tbl = process_stmt loop_desc.loop_prebody disam_tbl in
      let disam_tbl = DisambiguationTbl.pop disam_tbl in

      let* loop_test = disambiguate_process_expr loop_desc.loop_test Type.bool disam_tbl in

      let disam_tbl = DisambiguationTbl.push disam_tbl in
      let+ loop_postbody, locals'', disam_tbl = process_stmt loop_desc.loop_postbody disam_tbl in
      let disam_tbl = DisambiguationTbl.pop disam_tbl in

      (* Actually think about what variables need to be collected in `locals`. What if same variable is declared in multiple scopes in a callable, do all of them go in the `call_decl.call_decl_locals`? TW: I would say yes, unless you already have that information in the SymbolTable and always lookup locals through that. *)

      let (loop_desc: Stmt.loop_desc) = {
        loop_contract;
        loop_prebody;
        loop_test;
        loop_postbody;
      } in

      Stmt.Loop loop_desc, locals' @ locals'', disam_tbl

    | Cond cond_desc ->
      let* cond_test = disambiguate_process_expr cond_desc.cond_test Type.bool disam_tbl in

      let disam_tbl = DisambiguationTbl.push disam_tbl in
      let* cond_then, locals', disam_tbl = process_stmt cond_desc.cond_then disam_tbl in
      let disam_tbl = DisambiguationTbl.pop disam_tbl in

      let disam_tbl = DisambiguationTbl.push disam_tbl in
      let+ cond_else, locals'', disam_tbl = process_stmt cond_desc.cond_else disam_tbl in
      let disam_tbl = DisambiguationTbl.pop disam_tbl in

      let (cond_desc: Stmt.cond_desc) = {
        cond_test;
        cond_then;
        cond_else;
      } in

      Stmt.Cond cond_desc, locals' @ locals'', disam_tbl
    in
  
    Stmt.{stmt_desc = stmt_desc; stmt_loc = stmt.stmt_loc}, locals, disam_tbl

    in
    process_stmt ~new_scope stmt disam_tbl

  let process_callable (callable: Callable.t) : Module.symbol Rewriter.t =
    let open Rewriter.Syntax in
    let* _ = Rewriter.update_table (fun tbl -> SymbolTbl.enter callable.call_decl.call_decl_loc callable.call_decl.call_decl_name tbl) in    
    let disam_tbl = (DisambiguationTbl.push []) in
    let call_decl = Callable.to_decl callable in
    let process_decls var_decls disam_tbl =
      Rewriter.List.fold_map var_decls ~init:disam_tbl ~f:(
        fun disam_tbl var_decl -> 
          let+ var_decl = ProcessTypeExpr.process_var_decl var_decl in
          let var_decl', disam_tbl = DisambiguationTbl.add_var_decl var_decl disam_tbl in
          disam_tbl, var_decl'
      )
    in
    (* TODO: Add a check to make sure that all the implicit ghost variables are declared at the end. *)
    let* disam_tbl, call_decl_formals = process_decls call_decl.call_decl_formals disam_tbl in
    let* disam_tbl, call_decl_returns = process_decls call_decl.call_decl_returns disam_tbl in
    let* disam_tbl, call_decl_locals = process_decls call_decl.call_decl_locals disam_tbl in
    let* _ = Rewriter.add_locals call_decl_formals
    and* _ = Rewriter.add_locals call_decl_returns
    and* _ = Rewriter.add_locals call_decl_locals in
    let* call_decl_precond = Rewriter.List.map call_decl.call_decl_precond ~f:(process_stmt_spec disam_tbl)
    and* call_decl_postcond = Rewriter.List.map call_decl.call_decl_postcond ~f:(process_stmt_spec disam_tbl) in
    let call_decl =
      { call_decl with
        call_decl_formals;
        call_decl_returns;
        call_decl_locals;
        call_decl_precond;
        call_decl_postcond
      }
    in 
    let* callable = match callable.call_def with
      | FuncDef func_def ->
        (* FuncDefs should not have any new call_decl_locals in body because they are expressions. That is, all call_decl_locals are the arguments it takes. These are being disambiguated in the above.*)

        let+ func_body = Rewriter.map_opt func_def.func_body (fun expr ->
            let expected_return_type = Callable.return_type call_decl in
            disambiguate_process_expr expr expected_return_type disam_tbl)
        in

        let func_def =
          Callable.{
            call_decl;
            call_def = FuncDef { func_body };
          }
        in
        
        func_def 
          
      | ProcDef proc_def ->
        let expected_return_type = Callable.return_type call_decl in
        let+ proc_body, locals = match proc_def.proc_body with
        | None -> Rewriter.return (None, [])
        | Some stmt -> 
          let+ stmt, locals, _disam_tbl =
            process_stmt ~new_scope:false expected_return_type stmt disam_tbl
          in
          Some stmt, locals
        in
        
        let call_decl =
          { call_decl with
            call_decl_locals = call_decl.call_decl_locals @ locals
          }
        in
        
        let proc_def =
          Callable.{
            call_decl;
            call_def = ProcDef { proc_body };
          }
        in
        proc_def
    in
    let+ _ = Rewriter.update_table (fun tbl -> SymbolTbl.exit tbl) in
    Module.CallDef callable
  
      
end




module ProcessModule = struct
  (*let add_imports_to_tbl (imported_mod: Module.t) (tbl: SymbolTbl.t) : SymbolTbl.t =
    let tbl = Map.fold (imported_mod.mod_decl.mod_decl_fields) ~init:tbl ~f:(fun ~key:key ~data:data tbl -> SymbolTbl.add tbl (QualIdent.from_ident key) (Field data)) in

    let tbl = List.fold imported_mod.mod_defs imported_mod


      Map.fold (imported_mod.mod_decl.mod_decl_mod_defs) ~init:tbl ~f:(fun ~key:mod_name ~data:_mod_decl tbl -> 
      let orig_mod = Module.find_mod orig_imported_mod.members.mod_defs mod_name in
      let new_mod = Module.find_mod imported_mod.members.mod_defs mod_name in
      SymbolTbl.add tbl (QualIdent.from_ident mod_name) (ModDecl (new_mod, orig_mod))) in

    (* let tbl = Map.fold (imported_mod.module_decl.mod_decl_mod_aliases) ~init:tbl ~f:(fun ~key:key ~data:data tbl -> SymbolTbl.add tbl (QualIdent.from_ident key) (ModAlias data)) in *)

    let tbl = Map.fold (imported_mod.mod_decl.mod_decl_types) ~init:tbl ~f:(fun ~key:key ~data:data tbl -> SymbolTbl.add tbl (QualIdent.from_ident key) (TypeAlias data)) in

    let tbl = Map.fold (imported_mod.mod_decl.mod_decl_callables) ~init:tbl ~f:(fun ~key:key ~data:data tbl -> SymbolTbl.add tbl (QualIdent.from_ident key) (Callable data)) in

    let tbl = Map.fold (imported_mod.mod_decl.mod_decl_vars) ~init:tbl ~f:(fun ~key:key ~data:data tbl -> SymbolTbl.add tbl (QualIdent.from_ident key) (VarDecl data)) in

    tbl*)


  let rec process_type_def (type_def: Module.type_def) : Module.symbol Rewriter.t =
    let open Rewriter.Syntax in
    match type_def.type_def_expr with
    | None ->
      (* TW: is the following update needed? *)
      (*let tbl = SymbolTbl.set_global_symbol (QualIdent.from_ident type_def.type_def_name) Module.(TypeDef type_def) tbl in*)
      Rewriter.return Module.(TypeDef type_def)
    | Some tp_expr ->
      let+ tp_expr = 
        match tp_expr with
        | App (Data variant_decl_list, [], _tp_attr) ->
          (* _constr_map is constructed just to make sure no duplicate constructors are used in data type declaration. *)
          let _constr_map = List.fold variant_decl_list ~init:(Map.empty (module Ident))  ~f:(fun mp variant_decl -> 
            List.fold variant_decl.variant_args ~init:mp ~f:(fun mp var_arg ->
              match
                Map.add mp ~key:var_arg.var_name ~data:var_arg
              with
              | `Ok mp -> mp
              | `Duplicate -> Error.error (Type.to_loc tp_expr) @@ Printf.sprintf "Duplicate constructor found in data type %s" (Type.to_string tp_expr)
              )
          ) in

          let* variant_decl_list =
            Rewriter.List.map variant_decl_list ~f:(fun variant_decl -> 
                let+ variant_args = Rewriter.List.map variant_decl.variant_args ~f:(fun var_decl -> ProcessTypeExpr.process_var_decl var_decl) in
                { variant_decl with variant_args }
              )
          in

          let* fully_qualified_tp_name =
            Rewriter.resolve type_def.type_def_loc (QualIdent.from_ident type_def.type_def_name)
          in

          let+ _ =
            Rewriter.List.iter variant_decl_list ~f:(fun variant_decl -> 
                let* _ =
                  Rewriter.List.iter variant_decl.variant_args ~f:(fun var_arg ->
                      let (data_type_destr: Module.destr_def) = {
                        destr_name = var_arg.var_name;
                        destr_loc = var_arg.var_loc;
                        destr_arg = App (Var fully_qualified_tp_name, [], _tp_attr);
                        destr_return_type = var_arg.var_type;
                      }
                      in
                      Rewriter.introduce_symbol Module.(DestrDef data_type_destr)
                    )
                in

                let (data_type_constr: Module.constr_def) = {
                  constr_name = variant_decl.variant_name;
                  constr_loc = variant_decl.variant_loc;
                  constr_return_type = App (Var fully_qualified_tp_name, [], _tp_attr);
                  constr_args = variant_decl.variant_args;
                }
              
                in
              
                Rewriter.introduce_symbol Module.(ConstrDef data_type_constr)
              )
          in
          Type.App (Data variant_decl_list, [], _tp_attr)

          
        | App (Data _variant_decl_list, _, _tp_attr) ->
          Error.error (Type.to_loc tp_expr) ("Data types don't take arguments")

        | _ ->
          ProcessTypeExpr.process_type_expr tp_expr
      in
      
      let type_def =
        { type_def with
          type_def_expr = Some tp_expr;
        }
      in

      Module.TypeDef type_def

  let rec process_field (field: Module.field_def) : Module.symbol Rewriter.t=
    let open Rewriter.Syntax in
    let+ tp_expr = 
        match field.field_type with
        | App (Var qual_ident, [], tp_attr) ->
          let* fully_qualified_qual_ident, symbol =
            Rewriter.resolve_and_find (Type.loc field.field_type) qual_ident
          in
          (match Rewriter.Symbol.orig_symbol symbol with
          | ModDef { mod_decl = { mod_decl_is_ra = true; _ }; _ } ->
            Rewriter.return @@ Type.App (Var fully_qualified_qual_ident, [], tp_attr)

          | _ -> 
            ProcessTypeExpr.process_type_expr field.field_type
          )
        
        | _ ->  
          ProcessTypeExpr.process_type_expr field.field_type
      in

      let field = { field with field_type = tp_expr } in

      Module.(FieldDef field)

  let rec process_var (var: Stmt.var_def) : Module.symbol Rewriter.t = 
    let open Rewriter.Syntax in
    let* var_decl = ProcessTypeExpr.process_var_decl var.var_decl in
    let+ var_init = Rewriter.map_opt var.var_init (fun expr -> process_expr expr var_decl.var_type) in

    let (var: Stmt.var_def) = { var_decl; var_init } in

    Module.(VarDef var)

  (*
  let rec instantiate_module loc (m: Module.t) (tp_args: type_expr list) (tbl: SymbolTbl.t) : SymbolTbl.t * Module.t = 
    let rec instantiate_mod_helper loc (m: Module.t) (tp_args: type_expr list) (tbl: SymbolTbl.t): Module.t =
      (match tp_args, m.mod_decl.mod_decl_formals with
      | [], _ -> m
      | _tp_arg :: _, [] ->
        type_error loc (Ident.to_string m.mod_decl.mod_decl_name ^ " instantiated with too many arguments")
      | tp_arg :: tp_args, formal_mod_inst :: formals ->

        if Type.is_any formal_mod_inst.mod_inst_type || true then
          (* TODO: || does_module_implement_module (type_expr_to_mod_decl tp_arg tbl) (type_expr_to_mod_decl formal_mod_alias.mod_alias_type tbl)*)

          let new_inst = {formal_mod_inst with mod_inst_def = Some tp_arg} in

          let mod_decl = {m.mod_decl with
            mod_decl_formals = formals;
            mod_decl_mod_aliases = Map.set m.mod_decl.mod_decl_mod_aliases ~key: formal ~data:new_inst
          } in

          let instr = Module.SymbolDef (ModInst new_inst) :: m.mod_def in

          let (new_mod: Module.t) =
            { mod_decl = mod_decl;
              mod_def = instr;
              mod_interface = false;
            }
          in

          instantiate_mod_helper loc new_mod tp_args tbl
        
        else
          type_error (Type.loc tp_arg) ("Argument " ^ Type.to_string tp_arg ^ " does not match type " ^ Type.to_string formal_mod_inst.mod_inst_type ^ " for Module " ^ Ident.to_string m.mod_decl.mod_decl_name)

      
    ) in


    let instantiated_mod = instantiate_mod_helper loc m tp_args tbl in

    process_module instantiated_mod tbl
     
  and does_module_implement_module (_mod_decl: Module.module_decl) (_implemented_mod_decl: Module.module_decl) : bool = 
    true
    (* TODO *)

  and module_inst_to_module (mod_inst: Module.module_inst) (tbl: SymbolTbl.t) : SymbolTbl.t * Module.t =
    let tp_expr = 
      match mod_inst.mod_inst_def with
      | None -> mod_inst.mod_inst_type
      | Some tp_expr -> tp_expr

    in
    match tp_expr  with
    | App (Var mod_name, tp_args, _) ->
        let orig_mod = 
        (match SymbolTbl.find mod_name tbl with
        | Some (ModDef orig_mod) -> orig_mod
        | Some (ModInst mod_inst) ->
          Error.internal_error mod_inst.mod_inst_loc "Found ModInst in SymbolTbl for definition of mod_inst.";
        
        | _ ->
          Error.internal_error mod_inst.mod_inst_loc @@
            (Printf.sprintf "Unexpected elem found in typing env for type_expr %s of modAlias.\n\nTbl:%s" (Type.to_string tp_expr) (SymbolTbl.to_string tbl))
        ) in

        let new_mod_decl = 
          { orig_mod.mod_decl with
            mod_decl_name = mod_inst.mod_inst_name;
            mod_decl_loc = Type.loc tp_expr
          }
        in
        
        let new_mod =
          { orig_mod with
            mod_decl = new_mod_decl
          }
        in

        instantiate_module (Type.loc tp_expr) new_mod tp_args tbl

    | _ ->
      Error.internal_error mod_inst.mod_inst_loc
        @@ Printf.sprintf "Unexpected type_expr %s found in mod_alias_type for type of modAlias %s" (Type.to_string tp_expr) (Ident.to_string mod_inst.mod_inst_name)
    
  and process_mod_inst_tp_expr (tp_expr: type_expr) (tbl: SymbolTbl.t) (loc: Util.Loc.t): type_expr =
    (* This function is separate from process_tp_expr because in normal code, a Var type_expr is treated differently from a Var type_expr used as argument in mod_alias. *)
  match tp_expr with
  | App (Var qual_ident, tp_args, tp_attr) ->

    let tp_args = List.map tp_args ~f:(fun tp_arg -> process_mod_inst_tp_expr tp_arg tbl loc) in

    let fully_qualified_ident, symbol = 
        SymbolTbl.resolve_and_find_exn (Type.loc tp_expr) qual_ident tbl 
    in
    begin match symbol with
    | ModDef _ | TypeDef _ | ModInst _ ->
      Type.App (Var fully_qualified_ident, tp_args, tp_attr)
    | _ ->
      Error.error loc @@
        "Expected functor identifier, but found " ^ QualIdent.to_string fully_qualified_ident
    end
  
  | _ -> ProcessTypeExpr.process_type_expr tp_expr tbl
      
  
  and process_module_inst (mod_inst: Module.module_inst) (tbl: SymbolTbl.t) : SymbolTbl.t * Module.module_inst = 
    (* Mod_aliases will be instantiated to appropriate module_decl, and their expanded module_decl will be stored to the symbol tbl. In the actual AST itself, they will remain as mod_aliases. *)

    let mod_inst_type = 
      match mod_inst.mod_inst_type with
      | App (Bot, _, _) -> 
        mod_inst.mod_inst_type
      | App (Var _mod_name, _tp_args, _tp_attr) ->
        process_mod_inst_tp_expr mod_inst.mod_inst_type tbl mod_inst.mod_inst_loc

      | _ -> Error.type_error (mod_inst.mod_inst_loc) "Cannot instantiate this type to a module."
    in

    let mod_inst_def = 
      match mod_inst.mod_inst_def with
      | None -> None
      | Some tp_expr ->
        Some (process_mod_inst_tp_expr tp_expr tbl mod_inst.mod_inst_loc)
    in

    let mod_inst =
      { mod_inst with
        mod_inst_type = mod_inst_type;
        mod_inst_def = mod_inst_def;
      }
    in

    (* TODO: Make sure mod_inst_def actually implements mod_inst_type *)

    let tbl, derived_mod = module_inst_to_module mod_inst tbl in

    let tbl = SymbolTbl.set_symbol (ModDef derived_mod) tbl in

    tbl, mod_inst
  
   *)

  (*and process_mod_aliases (mod_aliases: Module.module_i list) (mod_decl: Module.module_decl) (tbl: SymbolTbl.t) : Module.module_alias list * Module.module_decl * SymbolTbl.t = 
    let (mod_decl, tbl), mod_aliases = List.fold_map mod_aliases ~init:(mod_decl, tbl) ~f:(fun (mod_decl, tbl) mod_alias ->
      let mod_alias, mod_decl, tbl = process_module_alias mod_alias mod_decl tbl in
      (mod_decl, tbl), mod_alias
    ) in

    mod_aliases, mod_decl, tbl*)

  let rec process_module (m: Module.t) : Module.t Rewriter.t =
    let open Rewriter.Syntax in
    let process_instr =
      function
      | Module.SymbolDef symbol ->
        let* symbol = match symbol with
          | TypeDef type_def -> 
            process_type_def type_def 
          | VarDef var_def -> process_var var_def
          | FieldDef field_def -> process_field field_def
          | ConstrDef _ | DestrDef _ -> Rewriter.return symbol (* These should not occur directly in a module definition *)
          | CallDef call_def -> ProcessCallable.process_callable call_def
          | ModDef mod_def ->
            let* _ = Rewriter.enter mod_def
            and* mod_def = process_module mod_def in
            let+ mod_def = Rewriter.exit mod_def in
            Module.ModDef mod_def
          | ModInst _ -> failwith "not implemented"
        in
        let+ _ = Rewriter.set_symbol symbol in
        Module.SymbolDef symbol
      | Import import -> (* handled earlier *)
        Rewriter.return (Module.Import import)
    in 

    let mod_def_formals =
      List.map m.mod_decl.mod_decl_formals
        ~f: (fun mod_def_formal -> Module.SymbolDef (ModInst mod_def_formal))
    in
    let mod_def = mod_def_formals @ m.mod_def in
    let* _ = Rewriter.List.map mod_def ~f:(function
        | Module.SymbolDef symbol -> Rewriter.declare_symbol symbol
        | Module.Import import -> Rewriter.import import) 
    in
    let mod_decl_rep = List.fold_left m.mod_def ~init:None
        ~f:(fun rep_type -> function
            | SymbolDef (TypeDef type_def) when type_def.type_def_rep ->
              Option.map_or_else 
                ~m:(fun _ -> Error.syntax_error type_def.type_def_loc (Some (Printf.sprintf !"Found more than one rep type in module %{Ident}" m.mod_decl.mod_decl_name)))
                ~e:(fun () -> Some type_def.type_def_name) () rep_type
            | _ -> rep_type)
    in
    (*  let* tbl = Rewriter.get_table in
      let tbl, mod_decl_type = ProcessTypeExpr.process_type_expr m.mod_decl.mod_decl_rep*)
    let mod_decl = { m.mod_decl with mod_decl_rep } in
    let+ mod_def = Rewriter.List.map m.mod_def ~f:process_instr in
    Module.{ m with mod_decl; mod_def }
    
    (*
    let formal_args_mod_aliases = mod_decl.mod_decl_formals in

    let _mod_aliases, mod_decl, tbl = process_mod_alias formal_args_mod_aliases mod_decl tbl in
    (* This is instantiating all formal arguments to the module. The process_mod_aliases is primarily called to add the requisite members to the tbl for processing the rest of the module. (It also fully modifies the mod_decl by expanding the modules names referenced in mod_aliases to fully qualified names.) The returned mod_aliases are not stored.  *)

    let mod_aliases, mod_decl, tbl = process_mod_aliases m.members.mod_aliases mod_decl tbl in

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

    let process_mod_decl (mod_decl, inherited_fields, inherited_types, inherited_vars, inherited_call_defs, tbl, is_ra) tp_expr =
      let tp_expr = process_mod_alias_tp_expr tp_expr tbl (Type.to_loc tp_expr) in 
      let (impl_alias: Module.module_alias) = {
        mod_alias_name = mod_decl.Module.mod_decl_name;
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
            let mod_decl =
              { mod_decl with
                mod_decl_fields = Map.set mod_decl.mod_decl_fields ~key:field_def.field_name ~data:field_def;
              }
            in

            let tbl = SymbolTbl.add tbl (QualIdent.from_ident field_def.field_name) (Field field_def) in

            field_def :: inherited_fields, mod_decl, tbl
          | Some field_def' -> 
            if Type.equal field_def'.field_type field_def.field_type then 
              (inherited_fields, mod_decl, tbl)
            else
              Error.error (Type.to_loc tp_expr) @@ Printf.sprintf "Module %s implementation of field %s incompatible with %s" (Ident.to_string mod_decl.mod_decl_name) (Ident.to_string field_name) (Type.to_string tp_expr)
        )
      in

      let inherited_types, mod_decl, tbl = Map.fold impl_mod.module_decl.mod_decl_types ~init:(inherited_types, mod_decl, tbl) ~f:(fun ~key:type_name ~data:type_def (inherited_types, mod_decl, tbl) ->
          match Map.find mod_decl.mod_decl_types type_name with
          | None -> 
            let mod_decl =
              { mod_decl with
                mod_decl_types = Map.set mod_decl.mod_decl_types ~key:type_def.type_alias_name ~data: type_def; 
              }
            in
            
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
        )
      in

      let inherited_vars, mod_decl, tbl = Map.fold impl_mod.module_decl.mod_decl_vars ~init:(inherited_vars, mod_decl, tbl) ~f:(fun ~key:var_name ~data:var_decl (inherited_vars, mod_decl, tbl) ->
          match Map.find mod_decl.mod_decl_vars var_name with
          | None -> 
            let var_def = Module.find_var impl_mod.members.vars var_name in
            
            let mod_decl =
              { mod_decl with
                mod_decl_vars = Map.set mod_decl.mod_decl_vars ~key:var_def.var_decl.var_name ~data:var_def.var_decl;
              }
            in
            
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
                  let mod_decl =
                    { mod_decl with
                      mod_decl_callables = Map.set mod_decl.mod_decl_callables ~key:proc_def.proc_decl.call_decl_name ~data:proc_def.proc_decl;
                    }
                  in

                  let tbl = SymbolTbl.add tbl (QualIdent.from_ident proc_def.proc_decl.call_decl_name) (Callable proc_def.proc_decl) in

                  impl_callable :: inherited_call_defs, mod_decl, tbl
                | None ->
                  if m.interface then
                    let mod_decl =
                      { mod_decl with
                        mod_decl_callables = Map.set mod_decl.mod_decl_callables ~key:proc_def.proc_decl.call_decl_name ~data:proc_def.proc_decl;
                      }
                    in

                    let tbl = SymbolTbl.add tbl (QualIdent.from_ident proc_def.proc_decl.call_decl_name) (Callable proc_def.proc_decl) in

                    impl_callable :: inherited_call_defs, mod_decl, tbl
                  else
                    (match proc_def.proc_decl.call_decl_kind with
                     | Lemma -> 
                       let proc_def =
                         { proc_def with
                           proc_body = Some (Stmt.mk_skip (Type.to_loc tp_expr));
                         }
                       in
                       
                       let mod_decl =
                         { mod_decl with
                           mod_decl_callables = Map.set mod_decl.mod_decl_callables ~key:proc_def.proc_decl.call_decl_name ~data:proc_def.proc_decl;
                         }
                       in

                       let tbl = SymbolTbl.add tbl (QualIdent.from_ident proc_def.proc_decl.call_decl_name) (Callable proc_def.proc_decl) in
                       
                       ProcDef proc_def :: inherited_call_defs, mod_decl, tbl

                     | _ -> Error.error (Type.to_loc tp_expr) @@ Printf.sprintf "Module %s does not implement callable %s -- incompatible with %s" (Ident.to_string mod_decl.mod_decl_name) (Ident.to_string call_name) (Type.to_string tp_expr)
                  )
                )
                
             | FuncDef func_def ->
               (match func_def.func_body with
                | Some _ -> 
                  let mod_decl =
                    { mod_decl with
                      mod_decl_callables = Map.set mod_decl.mod_decl_callables ~key:func_def.func_decl.call_decl_name ~data:func_def.func_decl;
                    }
                  in

                  let tbl = SymbolTbl.add tbl (QualIdent.from_ident func_def.func_decl.call_decl_name) (Callable func_def.func_decl) in

                  impl_callable :: inherited_call_defs, mod_decl, tbl
              | None ->
                if m.interface then
                  let mod_decl =
                    { mod_decl with
                      mod_decl_callables = Map.set mod_decl.mod_decl_callables ~key:func_def.func_decl.call_decl_name ~data:func_def.func_decl;
                    }
                  in

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
    in
    
    let mod_decl, inherited_fields, inherited_types, inherited_vars, inherited_call_defs, tbl, does_mod_impl_ra =
      List.fold mod_decl.mod_decl_returns ~init:(mod_decl, [], [], [], [], tbl, false)
        ~f:process_mod_decl
    in

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
    let tbl, mod_def =
      Rewrites.rewrite_compr_modules mod_def
        (SymbolTbl.resolve_exn mod_decl.mod_decl_loc (QualIdent.from_ident mod_decl.mod_decl_name) tbl)
    in
    
    mod_def*)
end

let process_module ?(tbl = SymbolTbl.create ()) (m: Module.t) = 
  assert (SymbolTbl.curr_is_root tbl);
  assert Ident.(m.mod_decl.mod_decl_name = QualIdent.to_ident (SymbolTbl.root_ident tbl));
  Rewriter.eval (ProcessModule.process_module m) tbl
