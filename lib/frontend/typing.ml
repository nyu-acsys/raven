open Base
open Ast
open Util
open Error

let type_mismatch_error loc exp_ty fnd_ty =
  Error.type_error loc
    (Printf.sprintf
       !"Expected an expression of type\n\
        \  %{Type}\n\
         but found an expression of type\n\
        \  %{Type}"
       exp_ty fnd_ty)

let arguments_to_string d =
  if d = 1 then "one argument" else Printf.sprintf "%d arguments" d

let tuple_arg_mismatch_error loc expected =
  Error.type_error loc
    (Printf.sprintf "Expected tuple with %d components" expected)

let module_arg_mismatch_error loc typ_constr expected =
  Error.type_error loc
    (Printf.sprintf "Module %s expects %s." (Type.to_name typ_constr)
       (arguments_to_string expected))

let unexpected_functor_error loc =
  Error.type_error loc "A functor cannot be instantiated in this context"

module ProcessTypeExpr = struct
  let rec process_type_expr (tp_expr : type_expr) : type_expr Rewriter.t =
    let open Type in
    let open Rewriter.Syntax in
    let loc = Type.to_loc tp_expr in
    match tp_expr with
    | App (Var qual_ident, [], tp_attr) -> (
        let+ fully_qualified_qual_ident, symbol =
          Rewriter.resolve_and_find loc qual_ident
        in
        match Rewriter.Symbol.orig_symbol symbol with
        | TypeDef _tp_alias -> App (Var fully_qualified_qual_ident, [], tp_attr)
        | ModDef m -> (
            match m.mod_decl.mod_decl_rep with
            | None ->
                Logs.debug (fun mm -> mm "%a" Ident.pr m.mod_decl.mod_decl_name);
                Error.type_error tp_attr.type_loc
                  ("Module "
                  ^ QualIdent.to_string qual_ident
                  ^ " does not have a rep type. It cannot be used in a context \
                     expecting a type")
            | Some rep_ident ->
                let rep_fully_qualified_qual_ident =
                  QualIdent.append fully_qualified_qual_ident rep_ident
                in
                App (Var rep_fully_qualified_qual_ident, [], tp_attr))
        | ModInst _ -> unexpected_functor_error tp_attr.type_loc
        | _ -> Error.type_error tp_attr.type_loc "Expected type identifier.")
    | App (Var _, _, tp_attr) -> unexpected_functor_error tp_attr.type_loc
    | App (((Set | Fld) as constr), tp_list, tp_attr) -> (
        match tp_list with
        | [ tp_arg ] ->
            let+ tp_arg' = process_type_expr tp_arg in
            App (constr, [ tp_arg' ], tp_attr)
        | _ -> module_arg_mismatch_error (Type.to_loc tp_expr) constr 1)
    | App (Map, tp_list, tp_attr) -> (
        match tp_list with
        | [ tp1; tp2 ] ->
            let+ tp1 = process_type_expr tp1 and+ tp2 = process_type_expr tp2 in
            App (Map, [ tp1; tp2 ], tp_attr)
        | _ -> module_arg_mismatch_error (Type.to_loc tp_expr) Map 2)
    | App (Data _, _tp_list, _tp_attr) ->
        (* The parser should prevent this from happening. *)
        Error.internal_error (Type.to_loc tp_expr)
          "Data types can only be defined as new types, not used inline"
    | App (Prod, tp_list, tp_attr) ->
        let+ tp_list = Rewriter.List.map tp_list ~f:process_type_expr in
        App (Prod, tp_list, tp_attr)
    | App (constr, [], tp_attr) -> Rewriter.return @@ App (constr, [], tp_attr)
    | App (constr, _tp_list, _tp_attr) ->
        (* The parser should prevent this from happening. *)
        Error.internal_error (Type.to_loc tp_expr)
          (Type.to_name constr ^ " types don't take arguments")

  let rec expand_type_expr (tp_expr : type_expr) : Type.t Rewriter.t =
    let open Rewriter.Syntax in
    match tp_expr with
    | App (constr, tp_expr_list, tp_attr) -> (
        match (constr, tp_expr_list) with
        | Var qual_iden, [] -> (
            (* Var types with args not supported. Polymorphic types need to be instantiated as separate modules before using. *)
            let* qual_ident, symbol =
              Rewriter.resolve_and_find (Type.to_loc tp_expr) qual_iden
            in
            let* qual_ident_def =
              Rewriter.Symbol.reify_type_def (Type.to_loc tp_expr) symbol
            in
            match qual_ident_def with
            | None ->
                Rewriter.return
                @@ Type.App (Var qual_ident, tp_expr_list, tp_attr)
            | Some (App (Data _, _, _)) ->
                Rewriter.return
                @@ Type.App (Var qual_ident, tp_expr_list, tp_attr)
            | Some tp_expr -> expand_type_expr tp_expr)
        | Var qual_iden, _ -> unexpected_functor_error tp_attr.type_loc
        | _ ->
            let+ expanded_tp_expr_list =
              Rewriter.List.map tp_expr_list ~f:expand_type_expr
            in
            Type.App (constr, expanded_tp_expr_list, tp_attr))

  let process_var_decl (var_decl : var_decl) : var_decl Rewriter.t =
    let open Rewriter.Syntax in
    if not (Type.equal var_decl.var_type Type.any) then
      let* var_type = process_type_expr var_decl.var_type in
      let+ var_type = expand_type_expr var_type in
      { var_decl with var_type }
    else
      Error.error var_decl.var_loc
      @@ Printf.sprintf "Type annotation missing for variable '%s'"
           (Ident.to_string var_decl.var_name)
end

(* TODO: move this function inside of process_expr *)
let check_and_set (expr : expr) (given_typ_lb : type_expr)
    (given_typ_ub : type_expr) (expected_typ : type_expr) : expr Rewriter.t =
  let open Rewriter.Syntax in
  let+ given_typ_lb =
    try ProcessTypeExpr.expand_type_expr given_typ_lb
    with Msg msgs ->
      Error.fail_with
        (List.map msgs ~f:(fun (lbl, _loc, msg) -> (lbl, Expr.to_loc expr, msg)))
  and+ given_typ_ub = ProcessTypeExpr.expand_type_expr given_typ_ub
  and+ expected_typ = ProcessTypeExpr.expand_type_expr expected_typ in
  let typ = Type.meet given_typ_ub expected_typ in
  if Type.subtype_of given_typ_lb typ then Expr.set_type expr typ
  else type_mismatch_error (Expr.to_loc expr) expected_typ given_typ_ub

(** Infer and check type of [expr] subject to typing environment [tbl] and expected type [expected_typ] *)
let rec process_expr (expr : expr) (expected_typ : type_expr) : expr Rewriter.t
    =
  let open Rewriter.Syntax in
  match expr with
  | App (constr, expr_list, expr_attr) -> (
      match (constr, expr_list) with
      (* Constants *)
      | (Null | Real _ | Int _ | Bool _ | Empty), [] ->
          let given_type_lb, given_type_ub =
            match constr with
            | Null -> (Type.ref, Type.ref)
            | Real _ -> (Type.real, Type.real)
            | Int _ -> (Type.int, Type.int)
            | Bool _ -> (Type.bool, Type.bool)
            | Empty ->
                ( Type.(mk_set (Expr.to_loc expr) bot),
                  Type.(mk_set (Expr.to_loc expr) any) )
            | _ -> assert false
          in
          check_and_set expr given_type_lb given_type_ub expected_typ
      | (Null | Real _ | Int _ | Bool _ | Empty), _expr_list ->
          Error.type_error (Expr.to_loc expr)
            (Expr.constr_to_string constr ^ " takes no arguments")
      (* Variables, fields, and call expressions *)
      | Var qual_ident, args_list -> (
          let* qual_ident, symbol =
            Rewriter.resolve_and_find (Expr.to_loc expr) qual_ident
          in
          (*let _ = Logs.debug (fun m -> m !"process_expr: ident: %{QualIdent}" qual_ident) in*)
          let* symbol = Rewriter.Symbol.reify symbol in
          match symbol with
          | ConstrDef _constr ->
              process_expr
                (App (DataConstr qual_ident, args_list, Expr.attr_of expr))
                expected_typ
          | CallDef callable ->
              let callable_decl = Callable.to_decl callable in
              let* args_list =
                process_callable_args (Expr.to_loc expr) callable_decl args_list
              in
              let given_typ = Callable.return_type callable_decl in
              let expr = Expr.App (Var qual_ident, args_list, expr_attr) in
              check_and_set expr given_typ given_typ expected_typ
          | VarDef _ | FieldDef _ ->
              let given_typ =
                match (symbol, args_list) with
                | VarDef var_def, [] -> var_def.var_decl.var_type
                | FieldDef field_def, [] -> field_def.field_type
                | _ ->
                    Error.type_error (Expr.to_loc expr)
                      (Printf.sprintf
                         !"Identifier %{QualIdent} cannot be called"
                         qual_ident)
              in
              let expr = Expr.App (Var qual_ident, [], expr_attr) in
              check_and_set expr given_typ given_typ expected_typ
          | _ ->
              Error.type_error (Expr.to_loc expr)
                ("Expected a variable, field, or callable identifier, but \
                  found "
                ^ QualIdent.to_string qual_ident))
      (* Unary expressions *)
      | (Not | Uminus), [ expr_arg ] ->
          let given_type_ub =
            match constr with
            | Uminus -> Type.num
            | Not -> Type.bool
            | _ -> assert false
          in
          let* expr_arg = process_expr expr_arg given_type_ub in
          let given_type_lb = Expr.to_type expr_arg in
          check_and_set
            (App (constr, [ expr_arg ], expr_attr))
            given_type_lb given_type_lb expected_typ
      | (Not | Uminus), _expr_list ->
          Error.type_error (Expr.to_loc expr)
            (Expr.constr_to_string constr ^ " takes exactly one argument")
      (* Binary expressions *)
      | ( ( TupleLookUp | MapLookUp | Diff | Union | Inter | Plus | Minus | Mult
          | Div | Mod | Gt | Lt | Geq | Leq | And | Or | Impl | Subseteq | Elem
          | Eq ),
          [ expr1; expr2 ] ) ->
          (* infer and propagated expected type of expr1 *)
          let expected_typ1 =
            match constr with
            | TupleLookUp -> Type.(any)
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
            | TupleLookUp -> Type.int
            | MapLookUp -> Type.map_dom typ1
            | Diff | Union | Inter | Plus | Minus | Mult | Div | Mod | Subseteq
            | Eq | Gt | Lt | Geq | Leq ->
                typ1
            | And | Or | Impl -> Type.perm
            | Elem -> Type.(set_typed typ1)
            | _ -> assert false
          in
          let* expr2 = process_expr expr2 expected_typ2 in
          let typ2 = Expr.to_type expr2 in

          (* backpropagate typ2 to expr1 if needed *)
          let expected_typ1 =
            match constr with
            | TupleLookUp ->
                let _lookup_type = Type.tuple_lookup typ1 (Expr.to_int expr2) in
                (* above lookup checks well-formedness of typ1 *)
                typ1
            | MapLookUp -> Type.(map typ2 (Type.map_codom typ1))
            | Diff | Union | Inter | Plus | Minus | Mult | Div | Mod | Subseteq
            | Eq | Gt | Lt | Geq | Leq ->
                typ2
            | And | Or | Impl -> Type.perm
            | Elem -> Type.set_elem typ2
            | _ -> assert false
          in
          let* expr1 =
            if Type.equal expected_typ1 typ1 then Rewriter.return expr1
            else process_expr expr1 expected_typ1
          in

          let expected_typ =
            if not @@ Type.is_any expected_typ then expected_typ
            else
              match constr with
              | TupleLookUp -> Type.tuple_lookup typ1 (Expr.to_int expr2)
              | MapLookUp -> Type.map_codom typ1
              | Diff | Union | Inter | Plus | Minus | Mult | Div | Mod -> typ2
              | And | Or | Impl -> expected_typ
              | Subseteq | Eq | Gt | Lt | Geq | Leq | Elem -> Type.bool
              | _ -> assert false
          in

          (* recompute expr and check against its expected type *)
          let given_typ_lb, given_typ_ub =
            match constr with
            | TupleLookUp ->
                let typ = Type.tuple_lookup typ1 (Expr.to_int expr2) in
                (typ, typ)
            | MapLookUp ->
                let typ = expr1 |> Expr.to_type |> Type.map_codom in
                (typ, typ)
            | Diff | Union | Inter ->
                (Type.(set_typed bot), Type.(set_typed any))
            | Plus | Minus | Mult | Div | Mod ->
                let typ = expr1 |> Expr.to_type in
                (typ, typ)
            | And | Or | Impl ->
                let typ = expr1 |> Expr.to_type in
                (Type.join typ typ2, Type.join typ typ2)
            | Subseteq | Elem | Eq | Gt | Lt | Geq | Leq ->
                (Type.bool, Type.bool)
            | _ -> assert false
          in
          check_and_set
            (App (constr, [ expr1; expr2 ], expr_attr))
            given_typ_lb given_typ_ub expected_typ
      | ( ( TupleLookUp | MapLookUp | Diff | Union | Inter | Plus | Minus | Mult
          | Div | Mod | And | Or | Impl | Subseteq | Elem | Eq | Gt | Lt | Geq
          | Leq ),
          _expr_list ) ->
          Error.type_error (Expr.to_loc expr)
            (Expr.constr_to_string constr ^ " takes exactly two arguments")
      (* Ternary expressions *)
      | (Ite | MapUpdate), [ expr1; expr2; expr3 ] ->
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
            | MapUpdate -> Type.map_codom typ1
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
            if Type.equal expected_typ2 typ2 then Rewriter.return expr2
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
            if Type.equal expected_typ1 typ1 then Rewriter.return expr1
            else process_expr expr1 expected_typ1
          in
          let typ1 = Expr.to_type expr1 in
          (* recompute expr and check against its expected type *)
          let given_typ_lb, given_typ_ub =
            match constr with
            | Ite -> (typ3, typ3)
            | MapUpdate -> (typ1, typ1)
            | _ -> assert false
          in
          let expr = Expr.App (constr, [ expr1; expr2; expr3 ], expr_attr) in
          check_and_set expr given_typ_lb given_typ_ub expected_typ
      | (Ite | MapUpdate), _expr_list ->
          Error.type_error (Expr.to_loc expr)
            (Expr.constr_to_string constr ^ " takes exactly three arguments")
      (* Ownership predicates *)
      | ( Own,
          expr1
          :: (App (Var qual_ident, [], expr_attr') as expr2)
          :: expr3 :: expr4_opt ) ->
          let* expr1 = process_expr expr1 Type.ref
          and* expr2 = process_expr expr2 Type.any in

          let field_type =
            match Expr.to_type expr2 with
            | App (Fld, [ tp_expr ], _) -> tp_expr
            | _ ->
                Error.type_error (Expr.to_loc expr2)
                  "Expected field identifier."
          in
          let* expr3 = process_expr expr3 field_type
          (* Implicitely case-split on heap RA vs. other RA *)
          and* expr4_opt =
            if List.length expr4_opt > 1 then
              Error.type_error (Expr.to_loc expr)
                "Own takes either three or four arguments."
            else
              Rewriter.List.map expr4_opt ~f:(fun e -> process_expr e Type.real)
          in
          (* Reconstruct and check expr *)
          let expr =
            Expr.App (Own, expr1 :: expr2 :: expr3 :: expr4_opt, expr_attr)
          in
          check_and_set expr Type.perm Type.perm expected_typ
      | Own, _expr_list ->
          Error.type_error (Expr.to_loc expr)
            (Expr.constr_to_string constr
            ^ " takes either three or four arguments, and second argument is a \
               field name.")
      | AUPred call_name, token :: args_list ->
          let loc = Expr.to_loc expr in
          let* call_name, symbol = Rewriter.resolve_and_find loc call_name in

          let* callable_decl =
            let+ symbol = Rewriter.Symbol.reify symbol in
            match symbol with
            | CallDef callable
              when Poly.(callable.call_decl.call_decl_kind = Proc) ->
                callable.call_decl
            | _ -> Error.type_error loc "Expected callable identifier"
          in

          if not (Callable.is_atomic callable_decl) then
            Error.type_error loc "Expected procedure with atomic specification"
          else
            let* token = process_expr token Type.atomic_token in
            let* args_list =
              process_callable_args loc callable_decl args_list
            in
            let expr =
              Expr.App (AUPred call_name, token :: args_list, expr_attr)
            in
            check_and_set expr Type.perm Type.perm expected_typ
      | AUPred _, [] ->
          Error.type_error (Expr.to_loc expr)
            "AUPred takes at least one argument"
      | AUPredCommit call_name, token :: args_list
        when List.length args_list >= 1 ->
          let loc = Expr.to_loc expr in
          let* call_name, symbol = Rewriter.resolve_and_find loc call_name in

          let* callable_decl =
            let+ symbol = Rewriter.Symbol.reify symbol in
            match symbol with
            | CallDef callable
              when Poly.(callable.call_decl.call_decl_kind = Proc) ->
                callable.call_decl
            | _ -> Error.type_error loc "Expected procedure identifier"
          in

          let ret_val = List.last_exn args_list in
          let args_list = List.drop_last_exn args_list in

          if not (Callable.is_atomic callable_decl) then
            Error.type_error loc "Expected procedure with atomic specification"
          else
            let* token = process_expr token Type.atomic_token in
            let* args_list =
              process_callable_args loc callable_decl args_list
            in
            let* ret_val =
              process_expr ret_val
                (Type.mk_prod loc
                   (List.map callable_decl.call_decl_returns ~f:(fun v ->
                        v.var_type)))
            in
            let expr =
              Expr.App (AUPred call_name, token :: args_list, expr_attr)
            in
            check_and_set expr Type.perm Type.perm expected_typ
      | AUPredCommit _, _ ->
          Error.type_error (Expr.to_loc expr)
            "AUPredCommit takes at least two arguments"
      (* Data constructor expressions *)
      | DataConstr constr_ident, args_list ->
          let loc = QualIdent.to_loc constr_ident in
          let* constr_decl =
            let* symbol = Rewriter.find loc constr_ident in
            let+ symbol = Rewriter.Symbol.reify symbol in
            match symbol with
            | ConstrDef constr -> constr
            | _ -> Error.type_error loc "Expected data constructor"
          in
          let constr_arg_types_list =
            List.map constr_decl.constr_args ~f:(fun var_decl ->
                var_decl.var_type)
          in
          let* maybe_args_list =
            Rewriter.List.map2 args_list constr_arg_types_list
              ~f:(fun expr tp_expr -> process_expr expr tp_expr)
          in
          let args_list =
            match maybe_args_list with
            | Ok list -> list
            | Unequal_lengths ->
                Error.type_error (Expr.to_loc expr)
                  ("data constructor "
                  ^ QualIdent.to_string constr_ident
                  ^ " called with incorrect number of arguments")
          in
          let given_typ = constr_decl.constr_return_type in
          let expr = Expr.App (constr, args_list, expr_attr) in
          check_and_set expr given_typ given_typ expected_typ
      (* Data destructor expressions *)
      | DataDestr destr_qual_ident, [ expr1 ] ->
          let loc = QualIdent.to_loc destr_qual_ident in
          let* destr =
            let* symbol = Rewriter.find loc destr_qual_ident in
            let+ symbol = Rewriter.Symbol.reify symbol in
            match symbol with
            | DestrDef destr -> destr
            | _tp_env -> Error.type_error loc "Expected data destructor"
          in
          let* expr1 = process_expr expr1 destr.destr_arg in
          let given_typ = destr.destr_return_type in
          let expr = Expr.App (constr, [ expr1 ], expr_attr) in
          check_and_set expr given_typ given_typ expected_typ
      | DataDestr _, _ ->
          Error.type_error (Expr.to_loc expr)
            (Expr.constr_to_string constr ^ " takes exactly one argument")
      (* Cas expressions *)
      | Cas, [ expr1; expr2; expr3 ] -> (
          match expr1 with
          | App
              ( Read,
                [ expr11; App (Var qual_ident, [], expr_attr') ],
                expr_attr'' ) -> (
              let* qual_ident, symbol =
                Rewriter.resolve_and_find (Expr.to_loc expr) qual_ident
              in
              let* symbol = Rewriter.Symbol.reify symbol in
              match symbol with
              | FieldDef { field_type = App (Fld, [ given_type ], _) as tp; _ }
                ->
                  let* expanded_type =
                    ProcessTypeExpr.expand_type_expr given_type
                  in
                  if
                    Type.(
                      expanded_type = int || expanded_type = bool
                      || expanded_type = ref)
                  then
                    let* expr11 = process_expr expr11 Type.ref in
                    let expr12 = Expr.App (Var qual_ident, [], expr_attr') in
                    let expr12 = Expr.set_type expr12 tp in
                    let* expr2 = process_expr expr2 given_type in
                    let* expr3 = process_expr expr3 given_type in
                    let expr1 =
                      Expr.App (Read, [ expr11; expr12 ], expr_attr'')
                    in
                    let expr1 = Expr.set_type expr1 given_type in
                    let expr =
                      Expr.App (Cas, [ expr1; expr2; expr3 ], expr_attr)
                    in
                    check_and_set expr Type.bool Type.bool expected_typ
                  else
                    Error.type_error (Expr.to_loc expr)
                      ("CAS only allowed over int, bool and ref; but found "
                     ^ Type.to_string given_type)
              | _ ->
                  Error.type_error (Expr.to_loc expr)
                    ("Expected field identifier, but found "
                    ^ QualIdent.to_string qual_ident))
          | _ ->
              Error.type_error (Expr.to_loc expr)
                ("Incorrect type in the first argument of "
                ^ Expr.constr_to_string constr))
      | Cas, _expr_list ->
          Error.type_error (Expr.to_loc expr)
            (Expr.constr_to_string constr ^ " takes exactly three arguments")
      (* Read expressions *)
      | Read, [ expr1; App (Var qual_ident, [], expr_attr') ] -> (
          let* qual_ident, symbol =
            Rewriter.resolve_and_find (Expr.to_loc expr) qual_ident
          in
          let* symbol = Rewriter.Symbol.reify symbol in
          match symbol with
          | DestrDef _ ->
              process_expr
                (App (DataDestr qual_ident, [ expr1 ], expr_attr))
                expected_typ
          | FieldDef { field_type = App (Fld, [ given_type ], _) as tp; _ } ->
              let* expr1 = process_expr expr1 Type.ref in
              let expr2 = Expr.App (Var qual_ident, [], expr_attr') in
              let expr2 = Expr.set_type expr2 tp in
              let expr = Expr.App (Read, [ expr1; expr2 ], expr_attr) in
              check_and_set expr given_type given_type expected_typ
          | _ ->
              Error.type_error (Expr.to_loc expr)
                ("Expected field or destructor identifier, but found "
                ^ QualIdent.to_string qual_ident))
      | Read, _expr_list ->
          Error.type_error (Expr.to_loc expr)
            (Expr.constr_to_string constr ^ " takes exactly two arguments")
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
            | App (Prod, ts, _) -> (
                List.zip elem_expr_list ts |> function
                | Ok res -> res
                | _ ->
                    tuple_arg_mismatch_error (Expr.to_loc expr) (List.length ts)
                )
            | _ -> List.map ~f:(fun e -> (e, Type.any)) elem_expr_list
          in
          let* elem_expr_list, elem_types =
            Rewriter.List.fold_right typed_elem_expr_list
              ~f:(fun (mexpr, mtyp) (elem_expr_list, elem_types) ->
                let+ mexpr = process_expr mexpr mtyp in
                (mexpr :: elem_expr_list, Expr.to_type mexpr :: elem_types))
              ~init:([], [])
          in
          let given_typ = Type.mk_prod (Expr.to_loc expr) elem_types in
          let expr = Expr.App (Tuple, elem_expr_list, expr_attr) in
          check_and_set expr given_typ given_typ expected_typ)
  | Binder (binder, var_decl_list, trgs, inner_expr, expr_attr) -> (
      let* var_decl_list =
        Rewriter.List.map var_decl_list ~f:(fun var_decl ->
            ProcessTypeExpr.process_var_decl var_decl)
      in
      let* _ = Rewriter.add_locals var_decl_list in

      match binder with
      | Forall | Exists ->
          let* inner_expr = process_expr inner_expr expected_typ in
          let* trgs =
            Rewriter.List.map trgs ~f:(fun trg ->
                Rewriter.List.map trg ~f:(fun expr ->
                    process_expr expr Type.any))
          in

          (* TODO: Add additional checks for triggers *)
          let inner_typ = Expr.to_type inner_expr in
          let expr =
            Expr.Binder (binder, var_decl_list, trgs, inner_expr, expr_attr)
          in
          check_and_set expr Type.bool Type.perm inner_typ
      | Compr ->
          let var_decl =
            match var_decl_list with
            | [ v ] -> v
            | _ ->
                Error.type_error (Expr.to_loc expr)
                  "Map/Set compr only take one quantified variable"
          in

          let inner_expr_expected_typ =
            match expected_typ with
            | App (Set, [ tp ], _) -> Type.bool
            | App (Map, [ _; tp ], _) -> tp
            | _tp ->
                Error.type_error (Expr.to_loc expr)
                  ("Expected set or map type; found " ^ Type.to_string _tp)
          in

          let* inner_expr = process_expr inner_expr inner_expr_expected_typ in
          let inner_expr_type = Expr.to_type inner_expr in

          let expr_typ =
            if Type.equal inner_expr_type Type.bool then
              Type.mk_set var_decl.var_loc var_decl.var_type
            else Type.mk_map var_decl.var_loc var_decl.var_type inner_expr_type
          in

          let expr =
            Expr.Binder (binder, var_decl_list, trgs, inner_expr, expr_attr)
          in
          check_and_set expr expr_typ expr_typ expected_typ)

(* end of process_expr *)

and process_callable_args loc callable_decl args_list =
  let callable_formals =
    match callable_decl.call_decl_kind with
    | Pred | Invariant ->
        callable_decl.call_decl_formals @ callable_decl.call_decl_returns
    | _ -> callable_decl.call_decl_formals
  in

  (* Check if too few arguments given. *)
  let _ =
    List.drop callable_formals (List.length args_list)
    |> List.exists ~f:(fun var_decl -> not @@ var_decl.Type.var_implicit)
    |> fun b ->
    if b then
      Error.type_error loc
      @@ Printf.sprintf "Some explicit arguments are missing in this call to %s"
           (Ident.to_string callable_decl.call_decl_name)
  in

  let provided_formals = List.take callable_formals (List.length args_list) in
  let explicit_formal_types =
    List.map provided_formals ~f:(fun var_decl ->
        (*ProcessTypeExpr.process_type_expr*) var_decl.Type.var_type)
  in
  let open Rewriter.Syntax in
  match%bind
    Rewriter.List.map2 args_list explicit_formal_types ~f:(fun expr tp_expr ->
        process_expr expr tp_expr)
  with
  | Ok args_list -> Rewriter.return args_list
  | Unequal_lengths ->
      (* Catches if too many args given. *)
      Error.type_error loc
      @@ Printf.sprintf "Too many arguments passed to %s"
           (Ident.to_string callable_decl.call_decl_name)

module ProcessCallable = struct
  module DisambiguationTbl = struct
    type t = ident ident_map list

    let push (disam_tbl : t) : t = Map.empty (module Ident) :: disam_tbl

    let pop (disam_tbl : t) : t =
      match disam_tbl with
      | _ :: disam_tbl -> disam_tbl
      | [] -> raise (Invalid_argument "Empty DisambiguationTbl")

    let add (disam_tbl : t) loc name new_name : t =
      match disam_tbl with
      | hd :: tl -> (
          match Map.add hd ~key:name ~data:new_name with
          | `Ok hd -> hd :: tl
          | `Duplicate -> Error.redeclaration_error loc (Ident.to_string name))
      | [] -> raise (Invalid_argument "Empty DisambiguationTbl")

    let rec find (disam_tbl : t) name =
      match disam_tbl with
      | [] -> None
      | map :: ts -> (
          match Map.find map name with
          | None -> find ts name
          | Some id -> Some id)

    let rec find_exn (disam_tbl : t) name =
      match disam_tbl with
      | map :: ts -> (
          match Map.find map name with
          | None -> find_exn ts name
          | Some id -> id)
      | [] -> raise Stdlib.Not_found

    let add_var_decl (var_decl : Type.var_decl) (disam_tbl : t) :
        Type.var_decl * t =
      let new_name =
        Ident.fresh var_decl.var_loc var_decl.var_name.ident_name
      in
      let disam_tbl =
        add disam_tbl var_decl.var_loc var_decl.var_name new_name
      in
      let var_decl = { var_decl with var_name = new_name } in

      (var_decl, disam_tbl)

    let pr ppf disam_tbl =
      let open Stdlib.Format in
      fprintf ppf "%a"
        (Fmt.Dump.list (Fmt.Dump.list (Fmt.Dump.pair Ident.pr Ident.pr)))
        (List.map disam_tbl ~f:Map.to_alist)
  end

  let disambiguate_ident (qual_ident : qual_ident)
      (disam_tbl : DisambiguationTbl.t) : qual_ident Rewriter.t =
    let open Rewriter.Syntax in
    if List.is_empty qual_ident.qual_path then
      let* base =
        if Predefs.is_qual_ident_au_cmnd qual_ident then
          Rewriter.return qual_ident.qual_base
        else
          match DisambiguationTbl.find disam_tbl qual_ident.qual_base with
          | Some iden -> Rewriter.return iden
          | None ->
              let* is_local =
                Rewriter.is_local qual_ident.qual_base.ident_loc qual_ident
              in
              if is_local then
                (* if variable is local and it doesn't exist in DisambiguationTbl, then it is not defined in scope *)
                error (QualIdent.to_loc qual_ident)
                @@ Printf.sprintf "Identifier %s unbound in scope"
                     (Ident.to_string qual_ident.qual_base)
              else Rewriter.return qual_ident.qual_base
      in
      Rewriter.return (QualIdent.make [] base)
    else Rewriter.return qual_ident

  let rec disambiguate_expr (expr : expr) (disam_tbl : DisambiguationTbl.t) :
      expr Rewriter.t =
    let open Rewriter.Syntax in
    match expr with
    | App (constr, expr_list, expr_attr) ->
        let* expr_list =
          Rewriter.List.map expr_list ~f:(fun expr ->
              disambiguate_expr expr disam_tbl)
        in

        let* constr =
          match constr with
          | Var qual_ident ->
              let+ qual_ident = disambiguate_ident qual_ident disam_tbl in
              Expr.Var qual_ident
          | DataConstr qual_ident ->
              let+ qual_ident = disambiguate_ident qual_ident disam_tbl in
              Expr.DataConstr qual_ident
          | DataDestr qual_ident ->
              let+ qual_ident = disambiguate_ident qual_ident disam_tbl in
              Expr.DataDestr qual_ident
          | _ -> Rewriter.return constr
        in
        Rewriter.return Expr.(App (constr, expr_list, expr_attr))
    | Binder (binder, var_decl_list, trgs, expr, expr_attr) ->
        let disam_tbl = DisambiguationTbl.push disam_tbl in
        let disam_tbl, var_decl_list =
          List.fold_map var_decl_list ~init:disam_tbl
            ~f:(fun disam_tbl var_decl ->
              let var_decl', disam_tbl =
                DisambiguationTbl.add_var_decl var_decl disam_tbl
              in
              (disam_tbl, var_decl'))
        in
        let* disambiguated_expr = disambiguate_expr expr disam_tbl in
        let* trgs =
          Rewriter.List.map trgs ~f:(fun trg ->
              Rewriter.List.map trg ~f:(fun expr ->
                  disambiguate_expr expr disam_tbl))
        in

        Rewriter.return
          Expr.(
            Binder (binder, var_decl_list, trgs, disambiguated_expr, expr_attr))

  let disambiguate_process_expr (expr : expr) (expected_typ : type_expr)
      (disam_tbl : DisambiguationTbl.t) : expr Rewriter.t =
    let open Rewriter.Syntax in
    let* expr = disambiguate_expr expr disam_tbl in
    process_expr expr expected_typ

  let process_stmt_spec (disam_tbl : DisambiguationTbl.t) (spec : Stmt.spec) :
      Stmt.spec Rewriter.t =
    let open Rewriter.Syntax in
    let+ spec_form =
      disambiguate_process_expr spec.spec_form Type.perm disam_tbl
    in
    { spec with spec_form }

  (* let rec purify_expr (expr: expr) (tbl: SymbolTbl.t) : Stmt.var_def list * expr =
     (* Takes an expr, and returns a pure expression along with a set of temp variables that need to be defined  *)
     () *)

  let process_au_action_stmt (stmt : Stmt.stmt_desc) (loc : location)
      (disam_tbl : DisambiguationTbl.t) :
      (Stmt.stmt_desc * DisambiguationTbl.t) Rewriter.t =
    let open Rewriter.Syntax in
    match stmt with
    | Basic (Assign assign_desc) -> (
        Logs.debug (fun m ->
            m "process_au_action_stmt: Assign: %a" Stmt.pr_basic_stmt
              (Assign assign_desc));
        match assign_desc.assign_rhs with
        | App (Var qual_ident, args, expr_attr) ->
            if
              QualIdent.(qual_ident = QualIdent.from_ident Predefs.bindAU_ident)
            then
              match (args, assign_desc.assign_lhs) with
              | [], [ token ] -> (
                  let+ token_expr =
                    disambiguate_process_expr token Type.atomic_token disam_tbl
                  in

                  match token_expr with
                  | App (Var token_qual_ident, [], _) ->
                      ( Stmt.Basic
                          (AUAction { auaction_kind = BindAU token_qual_ident }),
                        disam_tbl )
                  | _ ->
                      Error.type_error (Expr.to_loc token)
                        "The left-hand side of this ghost assignment must be a ghost variable")
              | _ -> Error.type_error loc "bindAU takes exactly one argument"
            else if
              QualIdent.(qual_ident = QualIdent.from_ident Predefs.openAU_ident)
            then
              
              let* bound_vars =
                Rewriter.List.map assign_desc.assign_lhs ~f:(fun expr ->
                    let+ expr =
                      disambiguate_process_expr expr Type.any disam_tbl
                    in
                    match expr with
                    | App (Var qual_ident, [], _) -> expr
                    | _ ->
                        Error.type_error loc
                          "openAU bound_variables expected to be a variable")
              in

              match args with
              | [ token ] -> (
                  let* token_expr =
                    disambiguate_process_expr token Type.atomic_token disam_tbl
                  in

                  match token_expr with
                  | App (Var token_qual_ident, [], _) ->
                      Rewriter.return
                        ( Stmt.Basic
                            (AUAction
                               {
                                 auaction_kind =
                                   OpenAU (token_qual_ident, None, bound_vars);
                               }),
                          disam_tbl )
                  | _ ->
                      Error.type_error loc
                        "openAU token expected to be a variable")
              | [ token; proc_name ] -> (
                  let* token_expr =
                    disambiguate_process_expr token Type.atomic_token disam_tbl
                  in
                  let+ proc_name_expr =
                    disambiguate_process_expr proc_name Type.any disam_tbl
                  in

                  match (token_expr, proc_name_expr) with
                  | ( App (Var token_qual_ident, [], _),
                      App (Var proc_qual_ident, [], _) ) ->
                      ( Stmt.Basic
                          (AUAction
                             {
                               auaction_kind =
                                 OpenAU
                                   ( token_qual_ident,
                                     Some proc_qual_ident,
                                     bound_vars );
                             }),
                        disam_tbl )
                  | _ ->
                      Error.type_error loc
                        "openAU token and process name expected to be a \
                         variable")
              | _ ->
                  Error.type_error loc
                    "openAU takes exactly one or two arguments"
            else if
              QualIdent.(
                qual_ident = QualIdent.from_ident Predefs.commitAU_ident)
            then
              match args with
              | token :: args -> (
                  let* token_expr =
                    disambiguate_process_expr token Type.atomic_token disam_tbl
                  in

                  let+ args =
                    Rewriter.List.map args ~f:(fun arg ->
                        disambiguate_process_expr arg Type.any disam_tbl)
                  in

                  match token_expr with
                  | App (Var token_qual_ident, [], _) ->
                      ( Stmt.Basic
                          (AUAction
                             {
                               auaction_kind = CommitAU (token_qual_ident, args);
                             }),
                        disam_tbl )
                  | _ ->
                      Error.type_error loc
                        "commitAU token expected to be a variable")
              | _ -> Error.type_error loc "commitAU takes at least one argument"
            else if
              QualIdent.(
                qual_ident = QualIdent.from_ident Predefs.abortAU_ident)
            then
              match args with
              | [ token ] -> (
                  let+ token_expr =
                    disambiguate_process_expr token Type.atomic_token disam_tbl
                  in

                  match token_expr with
                  | App (Var token_qual_ident, [], _) ->
                      ( Stmt.Basic
                          (AUAction { auaction_kind = AbortAU token_qual_ident }),
                        disam_tbl )
                  | _ ->
                      Error.type_error loc
                        "abortAU token expected to be a variable")
              | _ -> Error.type_error loc "abortAU takes exactly one argument"
            else if
              QualIdent.(qual_ident = QualIdent.from_ident Predefs.fpu_ident)
            then
              match args with
              | ref_expr :: field_expr :: fpu_exprs -> (
                  let* ref_expr =
                    disambiguate_process_expr ref_expr Type.ref disam_tbl
                  in
                  let* field_expr =
                    disambiguate_process_expr field_expr Type.any disam_tbl
                  in

                  match field_expr with
                  | App (Var field_qual_ident, [], _) -> (
                      let* field_symbol =
                        Rewriter.find_and_reify (Expr.to_loc field_expr)
                          field_qual_ident
                      in
                      match field_symbol with
                      | FieldDef
                          { field_type = App (Fld, [ given_type ], _); _ } ->
                          let+ fpu_exprs =
                            Rewriter.List.map fpu_exprs ~f:(fun fpu_expr ->
                                disambiguate_process_expr fpu_expr given_type
                                  disam_tbl)
                          in

                          (* let* old_val_expr = disambiguate_process_expr old_val_expr given_type disam_tbl in
                             let+ new_val_expr = disambiguate_process_expr new_val_expr given_type disam_tbl in *)
                          let old_val_expr, new_val_expr =
                            match fpu_exprs with
                            | [ old_val_expr; new_val_expr ] ->
                                (Some old_val_expr, new_val_expr)
                            | [ new_val_expr ] -> (None, new_val_expr)
                            | _ ->
                                Error.type_error loc
                                  "fpu takes exactly three or four arguments"
                          in

                          ( Stmt.Basic
                              (Fpu
                                 {
                                   fpu_ref = ref_expr;
                                   fpu_field = field_qual_ident;
                                   fpu_old_val = old_val_expr;
                                   fpu_new_val = new_val_expr;
                                 }),
                            disam_tbl )
                      | _ ->
                          Error.type_error loc
                            "fpu second argument expected to be a field name")
                  | _ ->
                      Error.type_error loc
                        "fpu second argument expected to be a field name")
              | _ ->
                  Error.type_error loc
                    "fpu takes exactly three or four arguments"
            else Error.type_error loc "Unknown AU action"
        | _ ->
            Error.error loc
              "Internal error: process_au_action_stmt called with non-callable \
               expression")
    | _ ->
        Error.error loc
          "Internal error: process_au_action_stmt called with non-assignment \
           statement"

  let process_stmt ?(new_scope = true) (expected_return_type : Type.t)
      (stmt : Stmt.t) (disam_tbl : DisambiguationTbl.t) :
      (Stmt.t * DisambiguationTbl.t) Rewriter.t =
    let rec process_stmt ?(new_scope = true) stmt disam_tbl =
      Logs.debug (fun m -> m "process_stmt: %a" Stmt.pr stmt);
      let open Rewriter.Syntax in
      let+ stmt_desc, disam_tbl =
        match stmt.Stmt.stmt_desc with
        | Block block_desc ->
            let disam_tbl =
              if new_scope then DisambiguationTbl.push disam_tbl else disam_tbl
            in

            let+ disam_tbl, stmt_list =
              Rewriter.List.fold_map block_desc.block_body ~init:disam_tbl
                ~f:(fun disam_tbl stmt ->
                  let+ stmt, disam_tbl = process_stmt stmt disam_tbl in
                  (disam_tbl, stmt))
            in

            let disam_tbl =
              if new_scope then DisambiguationTbl.pop disam_tbl else disam_tbl
            in

            (Stmt.Block { block_desc with block_body = stmt_list }, disam_tbl)
        | Basic basic_stmt -> (
            match basic_stmt with
            | VarDef var_def ->
                let* var_decl =
                  ProcessTypeExpr.process_var_decl var_def.var_decl
                in
                let var_decl, disam_tbl' =
                  DisambiguationTbl.add_var_decl var_decl disam_tbl
                in
                let* _ =
                  Rewriter.introduce_symbol
                    (VarDef { var_decl; var_init = None })
                in
                let+ stmt, disam_tbl' =
                  let var = QualIdent.from_ident var_decl.var_name in
                  match var_def.var_init with
                  | None ->
                      Rewriter.return @@ (Stmt.Basic (Havoc var), disam_tbl')
                  | Some expr ->
                      (* let* expr = disambiguate_process_expr expr var_decl.var_type disam_tbl in *)
                      let var_expr = Expr.from_var_decl var_def.var_decl in

                      (* Expr.App (Var var, [], {expr_loc = stmt.stmt_loc; expr_type = var_decl.var_type}) in *)
                      let assign_desc =
                        Stmt.
                          {
                            assign_lhs = [ var_expr ];
                            assign_rhs = expr;
                            assign_is_init = true;
                          }
                      in

                      let+ stmt, disam_tbl' =
                        process_stmt
                          {
                            stmt_desc = Stmt.Basic (Assign assign_desc);
                            stmt_loc = stmt.stmt_loc;
                          }
                          disam_tbl'
                      in

                      (stmt.stmt_desc, disam_tbl')
                in
                (stmt, disam_tbl')
            | Spec (sk, spec) ->
                let+ spec = process_stmt_spec disam_tbl spec in
                (Stmt.Basic (Spec (sk, spec)), disam_tbl)
            | Assign assign_desc -> (
                let* assign_lhs =
                  Rewriter.List.map assign_desc.assign_lhs ~f:(fun expr ->
                      disambiguate_process_expr expr Type.any disam_tbl)
                in

                let* _ =
                  Rewriter.List.iter assign_lhs ~f:(fun expr ->
                      match expr with
                      | App (Var qual_ident, [], _) -> (
                          let+ _, symbol =
                            Rewriter.resolve_and_find stmt.stmt_loc qual_ident
                          in
                          match Rewriter.Symbol.orig_symbol symbol with
                          | VarDef { var_decl = { var_const = true; _ }; _ }
                            when not assign_desc.assign_is_init ->
                              Error.type_error (Expr.to_loc expr)
                                "Cannot assign to val"
                          | VarDef _ -> ()
                          | _ ->
                              Error.type_error (Expr.to_loc expr)
                                "Expected assignable expression on left-hand \
                                 side of assignment")
                      | App (Read, [ ref_expr; field_expr ], _) ->
                          Rewriter.return ()
                      | _ ->
                          Error.type_error (Expr.to_loc expr)
                            "Expected assignable expression on left-hand side \
                             of assignment")
                in

                Logs.debug (fun m ->
                    m "process_stmt: assign_desc: %a" Stmt.pr_basic_stmt
                      (Assign assign_desc));
                let* disam_assign_rhs =
                  disambiguate_expr assign_desc.assign_rhs disam_tbl
                in

                Logs.debug (fun m ->
                    m "process_stmt: disam_assign_rhs: %a" Expr.pr
                      disam_assign_rhs);

                let* is_assign_rhs_callable =
                  match disam_assign_rhs with
                  | App (Var qual_ident, _, _) -> (
                      if Predefs.is_qual_ident_au_cmnd qual_ident then
                        Rewriter.return true
                      else
                        let+ _, symbol, _ =
                          Logs.debug (fun m ->
                              m
                                "process_stmt: disam_find: \
                                 assign_rhs_qual_ident: %a"
                                QualIdent.pr qual_ident);
                          Rewriter.find stmt.stmt_loc qual_ident
                        in
                        match symbol with CallDef _ -> true | _ -> false)
                  | _ -> Rewriter.return false
                in

                match is_assign_rhs_callable with
                | true -> (
                    match assign_desc.assign_rhs with
                    | App (Var proc_qual_ident, args, expr_attr) -> (
                        Logs.debug (fun m ->
                            m "process_stmt: assign_rhs_qual_ident: %a; %b"
                              QualIdent.pr proc_qual_ident
                              QualIdent.(
                                proc_qual_ident
                                = QualIdent.from_ident Predefs.bindAU_ident));
                        if Predefs.is_qual_ident_au_cmnd proc_qual_ident then
                          process_au_action_stmt stmt.stmt_desc stmt.stmt_loc
                            disam_tbl
                        else
                          let expected_return_type =
                            Type.mk_prod
                              (Expr.to_loc assign_desc.assign_rhs)
                              (List.map assign_lhs ~f:Expr.to_type)
                          in

                          let+ call_expr =
                            Expr.App (Var proc_qual_ident, args, expr_attr)
                            |> fun expr ->
                            disambiguate_process_expr expr expected_return_type
                              disam_tbl
                          in

                          match call_expr with
                          | App (Var proc_qual_ident, args, _expr_attr) ->
                              let (call_desc : Stmt.call_desc) =
                                {
                                  call_lhs =
                                    List.map assign_lhs ~f:Expr.to_qual_ident;
                                  call_name = proc_qual_ident;
                                  call_args = args;
                                }
                              in

                              (Stmt.Basic (Call call_desc), disam_tbl)
                          | _ ->
                              failwith "Unexpected error during type checking.")
                    | _ -> failwith "Unexpected error during type checking.")
                | false -> (
                    let expected_type =
                      Type.mk_prod stmt.stmt_loc
                        (List.map assign_lhs ~f:Expr.to_type)
                    in

                    let+ assign_rhs =
                      disambiguate_process_expr assign_desc.assign_rhs
                        expected_type disam_tbl
                    in

                    match assign_rhs with
                    | App (Read, [ ref_expr; field_expr ], _) ->
                        Logs.debug (fun m ->
                            m "process_stmt: read_assign_rhs: %a" Expr.pr
                              assign_rhs);
                        let field_qual_ident = Expr.to_qual_ident field_expr in
                        let field_read_lhs =
                          match assign_lhs with
                          | [ lhs ] -> Expr.to_qual_ident lhs
                          | _ ->
                              Error.type_error stmt.stmt_loc
                                "Expected exactly one left-hand side of field \
                                 read"
                        in

                        let field_read_desc =
                          Stmt.
                            {
                              field_read_lhs;
                              field_read_field = field_qual_ident;
                              field_read_ref = ref_expr;
                            }
                        in
                        (Stmt.Basic (FieldRead field_read_desc), disam_tbl)
                    | App
                        ( Cas,
                          [
                            App (Read, [ ref_expr; field_expr ], _);
                            old_val_expr;
                            new_val_expr;
                          ],
                          _ ) ->
                        Logs.debug (fun m ->
                            m "process_stmt: cas_assign_rhs: %a" Expr.pr
                              assign_rhs);
                        let field_qual_ident = Expr.to_qual_ident field_expr in
                        let cas_lhs =
                          match assign_lhs with
                          | [ lhs ] -> Expr.to_qual_ident lhs
                          | _ ->
                              Error.type_error stmt.stmt_loc
                                "Expected exactly one left-hand side of cas"
                        in

                        let cas_desc =
                          Stmt.
                            {
                              cas_lhs;
                              cas_field = field_qual_ident;
                              cas_ref = ref_expr;
                              cas_old_val = old_val_expr;
                              cas_new_val = new_val_expr;
                            }
                        in
                        (Stmt.Basic (Cas cas_desc), disam_tbl)
                    | _ ->
                        let assign_desc =
                          Stmt.{ assign_desc with assign_lhs; assign_rhs }
                        in

                        (Stmt.Basic (Assign assign_desc), disam_tbl)))
            | Bind bind_desc ->
                let* bind_lhs =
                  Rewriter.List.map bind_desc.bind_lhs ~f:(fun e ->
                      match e with
                      | App (Var qual_ident, [], _)
                        when not (QualIdent.is_qualified qual_ident) ->
                          disambiguate_process_expr e Type.any disam_tbl
                      | _ ->
                          Error.type_error stmt.stmt_loc
                            "Expected identifier on left-hand side of bind")
                in
                let* bind_rhs =
                  disambiguate_process_expr bind_desc.bind_rhs Type.any
                    disam_tbl
                in
                let bind_desc = Stmt.{ bind_lhs; bind_rhs } in
                Rewriter.return (Stmt.Basic (Bind bind_desc), disam_tbl)
            | FieldRead fr_desc -> (
                let* fr_var_qual_ident =
                  disambiguate_ident fr_desc.field_read_lhs disam_tbl
                in
                let* fr_var_qual_ident, symbol =
                  Rewriter.resolve_and_find stmt.stmt_loc fr_var_qual_ident
                in
                let* symbol = Rewriter.Symbol.reify symbol in
                let* fr_type =
                  match symbol with
                  | VarDef var_def ->
                      let* var_type_expanded =
                        ProcessTypeExpr.expand_type_expr
                          var_def.var_decl.var_type
                      in
                      Rewriter.return var_type_expanded
                  | _ ->
                      Error.type_error stmt.stmt_loc
                        "Expected variable identifier on left-hand side of \
                         field read"
                in
                let field_read_expr =
                  Expr.App
                    ( Read,
                      [
                        fr_desc.field_read_ref;
                        App
                          ( Var fr_desc.field_read_field,
                            [],
                            {
                              Expr.expr_loc = stmt.stmt_loc;
                              expr_type = Type.bot;
                            } );
                      ],
                      { Expr.expr_loc = stmt.stmt_loc; expr_type = Type.bot } )
                in

                let+ field_read_expr =
                  disambiguate_process_expr field_read_expr fr_type disam_tbl
                in

                match field_read_expr with
                | App
                    ( Read,
                      [ field_read_ref; App (Var field_read_field, [], _) ],
                      _ ) ->
                    let field_read_desc =
                      Stmt.
                        {
                          field_read_lhs = fr_var_qual_ident;
                          field_read_field;
                          field_read_ref;
                        }
                    in
                    (Stmt.Basic (FieldRead field_read_desc), disam_tbl)
                | _ -> failwith "Unexpected error during type checking.")
            | Cas cs_desc -> (
                let* cs_var_qual_ident =
                  disambiguate_ident cs_desc.cas_lhs disam_tbl
                in
                let* cs_var_qual_ident, symbol =
                  Rewriter.resolve_and_find stmt.stmt_loc cs_var_qual_ident
                in
                let* symbol = Rewriter.Symbol.reify symbol in
                let* cs_type =
                  match symbol with
                  | VarDef var_def ->
                      let* var_type_expanded =
                        ProcessTypeExpr.expand_type_expr
                          var_def.var_decl.var_type
                      in
                      Rewriter.return var_type_expanded
                  | _ ->
                      Error.type_error stmt.stmt_loc
                        "Expected variable identifier on left-hand side of CAS"
                in
                let expr_attr =
                  { Expr.expr_loc = stmt.stmt_loc; expr_type = Type.bot }
                in
                let cas_expr =
                  Expr.App
                    ( Cas,
                      [
                        App
                          ( Read,
                            [
                              cs_desc.cas_ref;
                              App (Var cs_desc.cas_field, [], expr_attr);
                            ],
                            expr_attr );
                        cs_desc.cas_old_val;
                        cs_desc.cas_new_val;
                      ],
                      { Expr.expr_loc = stmt.stmt_loc; expr_type = Type.bool }
                    )
                in

                let+ cas_expr =
                  disambiguate_process_expr cas_expr cs_type disam_tbl
                in

                match cas_expr with
                | App
                    ( Cas,
                      [
                        App (Read, [ cas_ref; App (Var cas_field, [], _) ], _);
                        cas_old_val;
                        cas_new_val;
                      ],
                      _ ) ->
                    let cas_desc =
                      Stmt.
                        {
                          cas_lhs = cs_var_qual_ident;
                          cas_field;
                          cas_ref;
                          cas_old_val;
                          cas_new_val;
                        }
                    in
                    (Stmt.Basic (Cas cas_desc), disam_tbl)
                | _ -> failwith "Unexpected error during type checking.")
            | Havoc qual_ident ->
                let* qual_ident = disambiguate_ident qual_ident disam_tbl in
                Rewriter.return (Stmt.Basic (Havoc qual_ident), disam_tbl)
            | Return expr ->
                let+ expr =
                  disambiguate_process_expr expr expected_return_type disam_tbl
                in
                (Stmt.Basic (Return expr), disam_tbl)
            | Use use_desc ->
                let* use_name, symbol =
                  let* id = disambiguate_ident use_desc.use_name disam_tbl in
                  Rewriter.resolve_and_find stmt.stmt_loc id
                in
                let* symbol = Rewriter.Symbol.reify symbol in

                let pred_decl =
                  match (symbol, use_desc.use_kind) with
                  | ( CallDef
                        {
                          call_decl = { call_decl_kind = Pred; _ } as pred_decl;
                          _;
                        },
                      (Fold | Unfold) ) ->
                      pred_decl
                  | ( CallDef
                        {
                          call_decl =
                            { call_decl_kind = Invariant; _ } as pred_decl;
                          _;
                        },
                      (Fold | Unfold) ) ->
                      pred_decl
                  (* | CallDef { call_decl = ({call_decl_kind = Invariant; _} as pred_decl); _ }, (OpenInv | CloseInv) -> pred_decl *)
                  | _, (Fold | Unfold) ->
                      Error.type_error stmt.stmt_loc
                        ("Expected predicate identifier, but found "
                        ^ QualIdent.to_string use_name)
                  | _ ->
                      Error.type_error stmt.stmt_loc
                        ("Expected invariant identifier, but found "
                        ^ QualIdent.to_string use_name)
                in

                let* use_args =
                  Rewriter.List.map use_desc.use_args ~f:(fun expr ->
                      disambiguate_expr expr disam_tbl)
                in

                let+ use_args =
                  process_callable_args stmt.stmt_loc pred_decl use_args
                in

                ( Stmt.Basic (Use { use_desc with use_name; use_args }),
                  disam_tbl )
            | New new_desc ->
                let* new_qual_ident =
                  disambiguate_ident new_desc.new_lhs disam_tbl
                in
                let* new_qual_ident, symbol =
                  Rewriter.resolve_and_find stmt.stmt_loc new_qual_ident
                in
                let* symbol = Rewriter.Symbol.reify symbol in
                let var_decl =
                  match symbol with
                  | VarDef var_def -> var_def.var_decl
                  | _ ->
                      Error.type_error stmt.stmt_loc
                        "Expected variable identifier on left-hand side of new"
                in
                let* var_type_expanded =
                  ProcessTypeExpr.expand_type_expr var_decl.var_type
                in

                if Type.equal var_type_expanded Type.ref then
                  let process_field_init (field_name, expr_opt) =
                    let* field_name, symbol =
                      Rewriter.resolve_and_find stmt.stmt_loc field_name
                    in
                    let* field_type =
                      Rewriter.Symbol.reify_field_type stmt.stmt_loc symbol
                    in
                    let+ expr_opt =
                      Rewriter.Option.map expr_opt ~f:(fun expr ->
                          disambiguate_process_expr expr field_type disam_tbl)
                    in
                    (field_name, expr_opt)
                  in
                  let+ new_args =
                    Rewriter.List.map new_desc.new_args ~f:process_field_init
                  in

                  let new_desc = Stmt.{ new_lhs = new_qual_ident; new_args } in

                  (Stmt.Basic (New new_desc), disam_tbl)
                else
                  type_mismatch_error stmt.stmt_loc Type.ref var_decl.var_type
            (* The following constructs are not expected here because the parser stores these commands as Assign stmts.
               The job of this function is to intercept the Assign stmts with the specific expressions on the RHS, and then transform
               them to the appropriate construct, ie Call, New, BindAU, OpenAU, AbortAU, CommitAU etc.

               This function is not expected to go over these parts of the AST again. If the following constructs are
               discovered by this function, then something unexpected has happened. *)
            (* Now that we call process_symbol on arbitrarily AST elements, we need to deal with these constructs too *)
            | Call call_desc -> (
                let* call_lhs =
                  Rewriter.List.map call_desc.call_lhs ~f:(fun qual_iden ->
                      let* qual_iden = disambiguate_ident qual_iden disam_tbl in
                      Rewriter.resolve stmt.stmt_loc qual_iden)
                in
                let* call_lhs_types =
                  Rewriter.List.map call_lhs ~f:(fun qual_iden ->
                      let* qual_iden, symbol =
                        Rewriter.resolve_and_find stmt.stmt_loc qual_iden
                      in
                      let* symbol = Rewriter.Symbol.reify symbol in
                      match symbol with
                      | VarDef var_def ->
                          let* var_type_expanded =
                            ProcessTypeExpr.expand_type_expr
                              var_def.var_decl.var_type
                          in
                          Rewriter.return var_type_expanded
                      | _ ->
                          Error.type_error stmt.stmt_loc
                            "Expected variable identifier on left-hand side of \
                             call")
                in

                let expected_return_type =
                  Type.mk_prod stmt.stmt_loc call_lhs_types
                in

                let+ call_expr =
                  Expr.App
                    ( Var call_desc.call_name,
                      call_desc.call_args,
                      { Expr.expr_loc = stmt.stmt_loc; expr_type = Type.bot } )
                  |> fun expr ->
                  disambiguate_process_expr expr expected_return_type disam_tbl
                in

                match call_expr with
                | App (Var proc_qual_ident, args, _expr_attr) ->
                    let (call_desc : Stmt.call_desc) =
                      {
                        call_lhs;
                        call_name = proc_qual_ident;
                        call_args = args;
                      }
                    in

                    (Stmt.Basic (Call call_desc), disam_tbl)
                | _ -> failwith "Unexpected error during type checking.")
            | AUAction _au_action_kind ->
                internal_error (Stmt.to_loc stmt)
                  "Did not expect AU action stmts in AST at this stage."
            | Fpu _fpu_desc ->
                internal_error (Stmt.to_loc stmt)
                  "Did not expect Fpu stmts in AST at this stage.")
        | Loop loop_desc ->
            let* loop_contract =
              Rewriter.List.map loop_desc.loop_contract
                ~f:(process_stmt_spec disam_tbl)
            in

            let disam_tbl = DisambiguationTbl.push disam_tbl in
            let* loop_prebody, disam_tbl =
              process_stmt loop_desc.loop_prebody disam_tbl
            in
            let disam_tbl = DisambiguationTbl.pop disam_tbl in

            let* loop_test =
              disambiguate_process_expr loop_desc.loop_test Type.bool disam_tbl
            in

            let disam_tbl = DisambiguationTbl.push disam_tbl in
            let+ loop_postbody, disam_tbl =
              process_stmt loop_desc.loop_postbody disam_tbl
            in
            let disam_tbl = DisambiguationTbl.pop disam_tbl in

            (* Actually think about what variables need to be collected in `locals`. What if same variable is declared in multiple scopes in a callable, do all of them go in the `call_decl.call_decl_locals`? TW: I would say yes, unless you already have that information in the SymbolTable and always lookup locals through that. *)
            let (loop_desc : Stmt.loop_desc) =
              { loop_contract; loop_prebody; loop_test; loop_postbody }
            in

            (Stmt.Loop loop_desc, disam_tbl)
        | Cond cond_desc ->
            let* cond_test =
              Rewriter.Option.map
                ~f:(fun test ->
                  disambiguate_process_expr test Type.bool disam_tbl)
                cond_desc.cond_test
            in

            let disam_tbl = DisambiguationTbl.push disam_tbl in
            let* cond_then, disam_tbl =
              process_stmt cond_desc.cond_then disam_tbl
            in
            let disam_tbl = DisambiguationTbl.pop disam_tbl in

            let disam_tbl = DisambiguationTbl.push disam_tbl in
            let+ cond_else, disam_tbl =
              process_stmt cond_desc.cond_else disam_tbl
            in
            let disam_tbl = DisambiguationTbl.pop disam_tbl in

            let (cond_desc : Stmt.cond_desc) =
              { cond_desc with cond_test; cond_then; cond_else }
            in

            (Stmt.Cond cond_desc, disam_tbl)
      in

      (Stmt.{ stmt_desc; stmt_loc = stmt.stmt_loc }, disam_tbl)
    in

    process_stmt ~new_scope stmt disam_tbl

  let process_callable (callable : Callable.t) : Module.symbol Rewriter.t =
    let open Rewriter.Syntax in
    Logs.debug (fun m ->
        m "Typing.process_callable: Start Processing callable: %a" Callable.pr
          callable);
    let* _ = Rewriter.enter_callable callable in
    let disam_tbl = DisambiguationTbl.push [] in
    let call_decl = Callable.to_decl callable in
    let process_decls var_decls disam_tbl =
      Rewriter.List.fold_map var_decls ~init:disam_tbl
        ~f:(fun disam_tbl var_decl ->
          let+ var_decl = ProcessTypeExpr.process_var_decl var_decl in
          let var_decl', disam_tbl =
            DisambiguationTbl.add_var_decl var_decl disam_tbl
          in
          (disam_tbl, var_decl'))
    in
    (* TODO: Add a check to make sure that all the implicit ghost variables are declared at the end. *)
    let* disam_tbl, call_decl_formals =
      process_decls call_decl.call_decl_formals disam_tbl
    in
    let* disam_tbl, call_decl_returns =
      process_decls call_decl.call_decl_returns disam_tbl
    in
    let* disam_tbl, call_decl_locals =
      process_decls call_decl.call_decl_locals disam_tbl
    in
    Logs.debug (fun m -> m "adding formals");
    let* _ = Rewriter.add_locals call_decl_formals in

    Logs.debug (fun m -> m "adding returns");
    let* _ = Rewriter.add_locals call_decl_returns in

    Logs.debug (fun m -> m "adding locals");
    let* _ = Rewriter.add_locals call_decl_locals in

    Logs.debug (fun m -> m "done adding locals");

    let* call_decl_precond =
      Rewriter.List.map call_decl.call_decl_precond
        ~f:(process_stmt_spec disam_tbl)
    and* call_decl_postcond =
      Rewriter.List.map call_decl.call_decl_postcond
        ~f:(process_stmt_spec disam_tbl)
    in
    let call_decl =
      {
        call_decl with
        call_decl_formals;
        call_decl_returns;
        call_decl_locals;
        call_decl_precond;
        call_decl_postcond;
      }
    in
    let* callable =
      match callable.call_def with
      | FuncDef func_def ->
          (* FuncDefs should not have any new call_decl_locals in body because they are expressions. That is, all call_decl_locals are the arguments it takes. These are being disambiguated in the above.*)
          let+ func_body =
            Rewriter.Option.map func_def.func_body ~f:(fun expr ->
                let expected_return_type = Callable.return_type call_decl in
                disambiguate_process_expr expr expected_return_type disam_tbl)
          in

          let func_def =
            Callable.{ call_decl; call_def = FuncDef { func_body } }
          in

          func_def
      | ProcDef proc_def ->
          let expected_return_type = Callable.return_type call_decl in
          let+ proc_body =
            Rewriter.Option.map proc_def.proc_body ~f:(fun stmt ->
                (* Logs.debug (fun m -> m "Typing.process_callable: Processing stmt: %a" Stmt.pr stmt); *)
                Logs.debug (fun m ->
                    m "Typing.process_callable: Callable: %a" Ident.pr
                      callable.call_decl.call_decl_name);

                Logs.debug (fun m ->
                    m "Typing.process_callable: DisamTbl: %a"
                      (Fmt.Dump.list
                         (Fmt.Dump.list (Fmt.Dump.pair Ident.pr Ident.pr)))
                      (List.map disam_tbl ~f:Map.to_alist));

                let+ stmt, _disam_tbl =
                  process_stmt ~new_scope:false expected_return_type stmt
                    disam_tbl
                in
                stmt)
          in

          let proc_def =
            Callable.{ call_decl; call_def = ProcDef { proc_body } }
          in
          proc_def
    in
    let+ callable = Rewriter.exit_callable callable in
    Module.CallDef callable
end

module ProcessModule = struct
  let process_type_def (type_def : Module.type_def) : Module.symbol Rewriter.t =
    let open Rewriter.Syntax in
    Logs.debug (fun m ->
        m "Typing.process_type_def: Start processing type_def: %a" Ident.pr
          type_def.type_def_name);
    match type_def.type_def_expr with
    | None -> Rewriter.return Module.(TypeDef type_def)
    | Some tp_expr ->
        let+ tp_expr =
          match tp_expr with
          | App (Data (_, variant_decl_list), [], _tp_attr) ->
              let* fully_qualified_tp_name =
                Rewriter.resolve type_def.type_def_loc
                  (QualIdent.from_ident type_def.type_def_name)
              in

              (* _constr_map is constructed just to make sure no duplicate constructors are used in data type declaration. *)
              let _constr_map =
                List.fold variant_decl_list
                  ~init:(Map.empty (module Ident))
                  ~f:(fun mp variant_decl ->
                    List.fold variant_decl.variant_args ~init:mp
                      ~f:(fun mp var_arg ->
                        match
                          Map.add mp ~key:var_arg.var_name ~data:var_arg
                        with
                        | `Ok mp -> mp
                        | `Duplicate ->
                            Error.error (Type.to_loc tp_expr)
                            @@ Printf.sprintf
                                 "Duplicate constructor found in data type %s"
                                 (Type.to_string tp_expr)))
              in

              let* variant_decl_list =
                Rewriter.List.map variant_decl_list ~f:(fun variant_decl ->
                    let+ variant_args =
                      Rewriter.List.map variant_decl.variant_args
                        ~f:(fun var_decl ->
                          ProcessTypeExpr.process_var_decl var_decl)
                    in
                    { variant_decl with variant_args })
              in

              let* fully_qualified_tp_name =
                Rewriter.resolve type_def.type_def_loc
                  (QualIdent.from_ident type_def.type_def_name)
              in

              let+ _ =
                Rewriter.List.iter variant_decl_list ~f:(fun variant_decl ->
                    let* _ =
                      Rewriter.List.iter variant_decl.variant_args
                        ~f:(fun var_arg ->
                          let (data_type_destr : Module.destr_def) =
                            {
                              destr_name = var_arg.var_name;
                              destr_loc = var_arg.var_loc;
                              destr_arg =
                                App (Var fully_qualified_tp_name, [], _tp_attr);
                              destr_return_type = var_arg.var_type;
                            }
                          in
                          Rewriter.introduce_symbol
                            Module.(DestrDef data_type_destr))
                    in

                    let (data_type_constr : Module.constr_def) =
                      {
                        constr_name = variant_decl.variant_name;
                        constr_loc = variant_decl.variant_loc;
                        constr_return_type =
                          App (Var fully_qualified_tp_name, [], _tp_attr);
                        constr_args = variant_decl.variant_args;
                      }
                    in

                    Rewriter.introduce_symbol
                      Module.(ConstrDef data_type_constr))
              in
              Type.App
                (Data (fully_qualified_tp_name, variant_decl_list), [], _tp_attr)
          | App (Data _, _, _tp_attr) ->
              Error.error (Type.to_loc tp_expr)
                "Data types don't take arguments"
          | _ -> ProcessTypeExpr.process_type_expr tp_expr
        in

        let type_def = { type_def with type_def_expr = Some tp_expr } in
        Module.TypeDef type_def

  let process_field (field : Module.field_def) : Module.symbol Rewriter.t =
    let open Rewriter.Syntax in
    let+ tp_expr =
      match field.field_type with
      | App (Var qual_ident, [], tp_attr) -> (
          let* fully_qualified_qual_ident, symbol =
            Rewriter.resolve_and_find (Type.to_loc field.field_type) qual_ident
          in
          match Rewriter.Symbol.orig_symbol symbol with
          | ModDef { mod_decl = { mod_decl_is_ra = true; _ }; _ } ->
              Rewriter.return
              @@ Type.App (Var fully_qualified_qual_ident, [], tp_attr)
          | _ -> ProcessTypeExpr.process_type_expr field.field_type)
      | _ -> ProcessTypeExpr.process_type_expr field.field_type
    in

    let field = { field with field_type = tp_expr } in
    Module.(FieldDef field)

  let process_var (var : Stmt.var_def) : Module.symbol Rewriter.t =
    let open Rewriter.Syntax in
    let* var_decl = ProcessTypeExpr.process_var_decl var.var_decl in
    let+ var_init =
      Rewriter.Option.map var.var_init ~f:(fun expr ->
          process_expr expr var_decl.var_type)
    in

    let (var : Stmt.var_def) = { var_decl; var_init } in

    Module.(VarDef var)

  let check_implements_symbol interface_ident (symbol : Symbol.t)
      (orig_symbol : Symbol.t) : unit Rewriter.t =
    let open Rewriter.Syntax in
    let loc = Symbol.to_loc symbol in
    let ident = Symbol.to_name symbol in
    match (symbol, orig_symbol) with
    | TypeDef typ_def, TypeDef orig_typ_def -> (
        if Bool.(typ_def.type_def_rep <> orig_typ_def.type_def_rep) then
          Error.type_error loc
            (Printf.sprintf
               !"Cannot change rep type annotation for type %{Ident} inherited \
                 from interface %{QualIdent}"
               ident interface_ident)
        else
          match (typ_def.type_def_expr, orig_typ_def.type_def_expr) with
          | None, Some _ ->
              Error.type_error loc
                (Printf.sprintf
                   !"Type %{Ident} cannot be redeclared as abstract. It was \
                     already defined in interface %{QualIdent}"
                   ident interface_ident)
          | Some _tp, Some _orig_tp ->
              Logs.debug (fun m -> m !"orig: %{Type}" _orig_tp);
              Error.type_error loc
                (Printf.sprintf
                   !"Type %{Ident} was already defined in interface \
                     %{QualIdent}"
                   ident interface_ident)
          | _ -> Rewriter.return ())
    | VarDef var_def, VarDef orig_var_def -> (
        if var_def.var_decl.var_ghost && not orig_var_def.var_decl.var_ghost
        then
          Error.type_error loc
            (Printf.sprintf
               !"Cannot redeclare %s %{Ident} from interface %{QualIdent} as \
                 ghost"
               (Symbol.kind symbol) ident interface_ident)
        else if
          (not var_def.var_decl.var_ghost) && orig_var_def.var_decl.var_ghost
        then
          Error.type_error loc
            (Printf.sprintf
               !"Cannot redeclare ghost %s %{Ident} from interface \
                 %{QualIdent} as non-ghost"
               (Symbol.kind symbol) ident interface_ident)
        else
          let* orig_var_def_var_type =
            ProcessTypeExpr.expand_type_expr orig_var_def.var_decl.var_type
          in

          if Type.(var_def.var_decl.var_type <> orig_var_def_var_type) then
            Error.type_error loc
              (Printf.sprintf
                 !"%s %{Ident} must have type %{Type} according to interface \
                   %{QualIdent}"
                 (Symbol.kind symbol |> String.capitalize)
                 ident orig_var_def.var_decl.var_type interface_ident)
          else
            match (var_def.var_init, orig_var_def.var_init) with
            | _, Some _ ->
                Error.type_error loc
                  (Printf.sprintf
                     !"%s %{Ident} was already defined in interface \
                       %{QualIdent}. It cannot be redefined."
                     (Symbol.kind symbol |> String.capitalize)
                     ident interface_ident)
            | _ -> Rewriter.return ())
    | CallDef call_def, CallDef orig_call_def -> (
        let make_subst decls odecls sm =
          Rewriter.List.fold2 decls odecls ~init:sm
            ~f:(fun sm (var_decl : var_decl) (ovar_decl : var_decl) ->
              let+ ovar_decl_var_type =
                ProcessTypeExpr.expand_type_expr ovar_decl.var_type
              in
              if
                Bool.(var_decl.var_const <> ovar_decl.var_const)
                || Bool.(var_decl.var_implicit <> ovar_decl.var_implicit)
                || Bool.(var_decl.var_ghost <> ovar_decl.var_ghost)
                || Type.(var_decl.var_type <> ovar_decl_var_type)
              then
                Error.type_error loc
                  (Printf.sprintf
                     !"Formal parameter %{Ident} of %s %{Ident} does not match \
                       parameter %{Ident} of %{Ident} in interface \
                       %{QualIdent}."
                     var_decl.var_name (Symbol.kind symbol) ident
                     ovar_decl.var_name ident interface_ident)
              else
                Map.add_exn sm
                  ~key:(QualIdent.from_ident ovar_decl.var_name)
                  ~data:(QualIdent.from_ident var_decl.var_name))
          |> fun ret_val ->
          match%bind ret_val with
          | Ok sm -> Rewriter.return sm
          | Unequal_lengths ->
              Error.type_error loc
                (Printf.sprintf
                   !"%s %{Ident} does not have the same number of parameters \
                     as %{Ident} in interface %{QualIdent}."
                   (Symbol.kind symbol) ident ident interface_ident)
        in

        if
          Poly.(
            call_def.call_decl.call_decl_kind
            <> orig_call_def.call_decl.call_decl_kind)
        then
          Error.type_error loc
            (Printf.sprintf
               !"Cannot redeclare %s %{Ident} from %{QualIdent} as %s."
               (Symbol.kind orig_symbol) ident interface_ident
               (Symbol.kind symbol))
        else
          let* sm =
            make_subst call_def.call_decl.call_decl_formals
              orig_call_def.call_decl.call_decl_formals
              (Map.empty (module QualIdent))
          in
          let pre_ok =
            List.for_all2 call_def.call_decl.call_decl_precond
              orig_call_def.call_decl.call_decl_precond
              ~f:(fun spec orig_spec ->
                Bool.(spec.spec_atomic = orig_spec.spec_atomic)
                && Expr.alpha_equal ~sm spec.spec_form orig_spec.spec_form)
            |> function
            | Ok res -> res
            | Unequal_lengths -> false
          in
          let _ =
            if not pre_ok then
              Error.type_error loc
                (Printf.sprintf
                   !"%s %{Ident} does not have the same precondition as \
                     %{Ident} in interface %{QualIdent}."
                   (Symbol.kind symbol) ident ident interface_ident)
          in
          let* sm =
            make_subst call_def.call_decl.call_decl_returns
              orig_call_def.call_decl.call_decl_returns sm
          in
          let post_ok =
            List.for_all2 call_def.call_decl.call_decl_postcond
              orig_call_def.call_decl.call_decl_postcond
              ~f:(fun spec orig_spec ->
                let post_ok =
                  Bool.(spec.spec_atomic = orig_spec.spec_atomic)
                  && Expr.alpha_equal ~sm spec.spec_form orig_spec.spec_form
                in
                post_ok)
            |> function
            | Ok res -> res
            | Unequal_lengths -> false
          in
          let _ =
            if not post_ok then
              Error.type_error loc
                (Printf.sprintf
                   !"%s %{Ident} does not have the same postcondition as \
                     %{Ident} in interface %{QualIdent}."
                   (Symbol.kind symbol) ident ident interface_ident)
          in
          match (call_def.call_def, orig_call_def.call_def) with
          | ProcDef { proc_body = Some _; _ }, ProcDef { proc_body = Some _; _ }
          | FuncDef { func_body = Some _; _ }, FuncDef { func_body = Some _; _ }
            ->
              Error.type_error loc
                (Printf.sprintf
                   !"%s %{Ident} was already defined in interface \
                     %{QualIdent}. It cannot be redefined."
                   (Symbol.kind symbol |> String.capitalize)
                   ident interface_ident)
          | ProcDef { proc_body = None; _ }, ProcDef { proc_body = Some _; _ }
          | FuncDef { func_body = None; _ }, FuncDef { func_body = Some _; _ }
            ->
              Error.type_error loc
                (Printf.sprintf
                   !"%s %{Ident} cannot be redeclared as abstract. It was \
                     already defined in interface %{QualIdent}"
                   (Symbol.kind symbol |> String.capitalize)
                   ident interface_ident)
          | _ -> Rewriter.return ())
    (*| ModDef mod_def, ModInst { mod_inst_def = Some (mod_inst_def_id, []); _ } ->
      let *)
    | ModDef mod_def, ModInst orig_mod_inst -> (
        if
          mod_def.mod_decl.mod_decl_is_interface
          && not orig_mod_inst.mod_inst_is_interface
        then
          Error.type_error loc
            (Printf.sprintf
               !"Cannot redeclare module %{Ident} from interface %{QualIdent} \
                 as interface"
               ident interface_ident)
        else if
          (not mod_def.mod_decl.mod_decl_is_interface)
          && orig_mod_inst.mod_inst_is_interface
        then
          Error.type_error loc
            (Printf.sprintf
               !"Cannot redeclare interface %{Ident} from interface \
                 %{QualIdent} as module"
               ident interface_ident)
        else
          let _ =
            match
              (mod_def.mod_decl.mod_decl_returns, orig_mod_inst.mod_inst_type)
            with
            | Some mod_typ, orig_mod_typ
              when QualIdent.(mod_typ <> orig_mod_typ) ->
                Error.type_error loc
                  (Printf.sprintf
                     !"%s %{Ident} must implement interface %{QualIdent} \
                       according to interface %{QualIdent}"
                     (Symbol.kind symbol |> String.capitalize)
                     ident orig_mod_inst.mod_inst_type interface_ident)
            | None, _ ->
                Error.type_error loc
                  (Printf.sprintf
                     !"%s %{Ident} must implement interface %{QualIdent} \
                       according to interface %{QualIdent}"
                     (Symbol.kind symbol |> String.capitalize)
                     ident orig_mod_inst.mod_inst_type interface_ident)
            | _ -> ()
          in
          if not @@ List.is_empty mod_def.mod_decl.mod_decl_formals then
            Error.type_error loc
              (Printf.sprintf
                 !"%s %{Ident} cannot have module parameters."
                 (Symbol.kind symbol |> String.capitalize)
                 ident)
          else
            match orig_mod_inst.mod_inst_def with
            | Some _ ->
                Error.type_error loc
                  (Printf.sprintf
                     !"%s %{Ident} was already defined in interface \
                       %{QualIdent}. It cannot be redefined."
                     (Symbol.kind symbol |> String.capitalize)
                     ident interface_ident)
            | _ -> Rewriter.return ())
    | ModInst mod_inst, ModInst orig_mod_inst -> (
        if
          mod_inst.mod_inst_is_interface
          && not orig_mod_inst.mod_inst_is_interface
        then
          Error.type_error loc
            (Printf.sprintf
               !"Cannot redeclare module %{Ident} from interface %{QualIdent} \
                 as interface"
               ident interface_ident)
        else if
          (not mod_inst.mod_inst_is_interface)
          && orig_mod_inst.mod_inst_is_interface
        then
          Error.type_error loc
            (Printf.sprintf
               !"Cannot redeclare interface %{Ident} from interface \
                 %{QualIdent} as module"
               ident interface_ident)
        else if
          QualIdent.(mod_inst.mod_inst_type <> orig_mod_inst.mod_inst_type)
        then
          Error.type_error loc
            (Printf.sprintf
               !"%s %{Ident} must implement interface %{QualIdent} according \
                 to interface %{QualIdent}"
               (Symbol.kind symbol |> String.capitalize)
               ident orig_mod_inst.mod_inst_type interface_ident)
        else
          match (mod_inst.mod_inst_def, orig_mod_inst.mod_inst_def) with
          | Some _, Some _ ->
              Error.type_error loc
                (Printf.sprintf
                   !"%s %{Ident} was already defined in interface \
                     %{QualIdent}. It cannot be redefined."
                   (Symbol.kind symbol |> String.capitalize)
                   ident interface_ident)
          | None, Some _ ->
              Error.type_error loc
                (Printf.sprintf
                   !"%s %{Ident} cannot be redeclared as abstract. It was \
                     already defined in interface %{QualIdent}"
                   (Symbol.kind symbol |> String.capitalize)
                   ident interface_ident)
          | _ -> Rewriter.return ())
    | ModDef _mod_def, ModDef _orig_mod_def ->
        Error.type_error loc
          (Printf.sprintf
             !"%s %{Ident} was already defined in interface %{QualIdent}. It \
               cannot be redefined."
             (Symbol.kind symbol |> String.capitalize)
             ident interface_ident)
    | _ ->
        Error.type_error loc
          (Printf.sprintf
             !"Cannot redeclare %s %{Ident} from interface %{QualIdent} as %s."
             (Symbol.kind orig_symbol) ident interface_ident
             (Symbol.kind symbol))

  let check_module_type mod_ident int_ident =
    let open Rewriter.Syntax in
    let+ qual_mod_ident, mod_symbol =
      Rewriter.resolve_and_find (QualIdent.to_loc mod_ident) mod_ident
    and+ qual_int_ident, _int_symbol =
      Rewriter.resolve_and_find (QualIdent.to_loc int_ident) int_ident
    in
    let interfaces =
      Rewriter.Symbol.extract mod_symbol ~f:(fun _subst -> function
        | Ast.Module.ModDef mod_def ->
            (*Set.map (module QualIdent) mod_def.mod_decl.mod_decl_interfaces ~f:subst*)
            mod_def.mod_decl.mod_decl_interfaces
        | _ -> Set.empty (module QualIdent))
    in
    if
      not
        (QualIdent.(qual_mod_ident = qual_int_ident)
        || Set.mem interfaces qual_int_ident)
    then
      Error.type_error
        (QualIdent.to_loc mod_ident)
        (Printf.sprintf
           !"%s %{QualIdent} does not implement interface %{QualIdent}."
           (Symbol.kind (Rewriter.Symbol.orig_symbol mod_symbol) |> String.capitalize)
           mod_ident int_ident)

  let rec process_module (m : Module.t) : Module.t Rewriter.t =
    let open Rewriter.Syntax in
    let _ =
      Logs.debug (fun mm ->
          mm !"Processing module %{Ident}" (Symbol.to_name (ModDef m)))
    in

    let* sc = Rewriter.current_scope_children in
    Logs.debug (fun mm ->
        mm
          !"Processing module %{Ident}: scope_children: %a"
          (Symbol.to_name (ModDef m))
          (Print.pr_list_comma Ident.pr)
          (Hashtbl.keys sc));
    let* is_root =
      let+ tbl = Rewriter.get_table in
      (* Hashtbl.mem  *)
      Ident.(
        m.mod_decl.mod_decl_name = QualIdent.to_ident (SymbolTbl.root_ident tbl))
    in

    let process_instr = function
      | Module.SymbolDef symbol ->
          let* symbol =
            match symbol with
            | TypeDef type_def -> process_type_def type_def
            | VarDef var_def -> process_var var_def
            | FieldDef field_def -> process_field field_def
            | ConstrDef _ | DestrDef _ ->
                Rewriter.return symbol
                (* These should not occur directly in a module definition *)
            | CallDef call_def -> ProcessCallable.process_callable call_def
            | ModDef mod_def ->
                let* _ = Rewriter.enter_module mod_def
                and* mod_def = process_module mod_def in
                let+ mod_def = Rewriter.exit_module mod_def in
                Module.ModDef mod_def
            | ModInst mod_inst ->
                let* to_check =
                  Rewriter.Option.map mod_inst.mod_inst_def
                    ~f:(fun (mod_inst_func, mod_inst_args) ->
                      let+ qual_functor_ident, functor_symbol =
                        Rewriter.resolve_and_find mod_inst.mod_inst_loc
                          mod_inst_func
                      in
                      let formals =
                        Rewriter.Symbol.extract functor_symbol ~f:(fun subst ->
                          function
                          | Ast.Module.ModDef mod_def ->
                              List.map mod_def.mod_decl.mod_decl_formals
                                ~f:(fun mod_inst ->
                                  subst mod_inst.mod_inst_type)
                          | _ -> [])
                      in
                      let args_and_formals =
                        match List.zip mod_inst_args formals with
                        | Ok res -> res
                        | Unequal_lengths ->
                            Error.type_error mod_inst.mod_inst_loc
                              (Printf.sprintf
                                 !"Module %{QualIdent} expects %d arguments"
                                 mod_inst_func (List.length formals))
                      in
                      args_and_formals
                      @ [ (qual_functor_ident, mod_inst.mod_inst_type) ])
                in
                let to_check = Option.value to_check ~default:[] in
                let+ _ =
                  Rewriter.List.iter to_check ~f:(fun (m, i) ->
                      check_module_type m i)
                in
                symbol
          in
          Logs.debug (fun mm ->
              mm
                !"Processing module %{Ident}: symbol: %a"
                (Symbol.to_name (ModDef m))
                Module.pr_symbol symbol);
          let+ _ = Rewriter.set_symbol symbol in
          Module.SymbolDef symbol
      | Import import ->
          (* Handled by symbol table *)
          Rewriter.return (Module.Import import)
    in

    (* Add formal parameters to module definitions *)
    let mod_def_formals =
      List.map m.mod_decl.mod_decl_formals ~f:(fun mod_def_formal ->
          Module.SymbolDef (ModInst mod_def_formal))
    in
    let mod_def = mod_def_formals @ m.mod_def in
    let get_defined_symbols mod_def =
      List.fold mod_def
        ~init:(Set.empty (module Ident))
        ~f:(fun ids -> function
          | Module.SymbolDef symbol -> Set.add ids (Symbol.to_name symbol)
          | _ -> ids)
    in
    let defined_symbols = get_defined_symbols mod_def in

    let* mod_qual_ident =
      if is_root then
        Rewriter.return @@ QualIdent.from_ident (Symbol.to_name (ModDef m))
      else
        let _ =
          Logs.debug (fun mm ->
              mm "Typing.process_module: computing mod_qual_ident: %a"
                QualIdent.pr
                (QualIdent.from_ident (Symbol.to_name (ModDef m))))
        in

        Rewriter.resolve m.mod_decl.mod_decl_loc
          (QualIdent.from_ident (Symbol.to_name (ModDef m)))
    in

    let merge_defs parent_ident parent_mod_def mod_def =
      let _parent_defined_symbols = get_defined_symbols parent_mod_def in
      let rec merge_defs (merged, to_check, seen) = function
        | [], mod_def -> (List.rev_append merged mod_def, to_check)
        | Module.Import _ :: parent_mod_def, mod_def ->
            merge_defs (merged, to_check, seen) (parent_mod_def, mod_def)
        | Module.SymbolDef (ConstrDef _ | DestrDef _) :: parent_mod_def, mod_def
          ->
            merge_defs (merged, to_check, seen) (parent_mod_def, mod_def)
        | parent_mod_def, Module.SymbolDef (ConstrDef _ | DestrDef _) :: mod_def
          ->
            merge_defs (merged, to_check, seen) (parent_mod_def, mod_def)
        | Module.SymbolDef parent_symbol :: parent_mod_def, mod_def -> (
            let parent_symbol_ident = Symbol.to_name parent_symbol in
            let annotate_error_msg = function
              | Module.CallDef ({ call_decl; _ } as call) as symbol ->
                let annotate_spec spec =
                  let error =
                    ( Error.Verification,
                      Symbol.to_loc parent_symbol,
                      (Printf.sprintf
                         !"%s %{Ident} inherited from %s %{QualIdent}.%{Ident}"
                         (Symbol.kind symbol |> String.capitalize)
                         parent_symbol_ident
                         (Symbol.kind parent_symbol)
                         parent_ident parent_symbol_ident))
                  in
                  { spec with Stmt.spec_error = Stmt.mk_const_spec_error error :: spec.Stmt.spec_error }
                in
                let call_decl_postcond = List.map ~f:annotate_spec call_decl.call_decl_postcond in
                let call_decl_precond = List.map ~f:annotate_spec call_decl.call_decl_precond in
                let call_decl =
                  { call_decl with
                    call_decl_precond;
                    call_decl_postcond;
                    call_decl_loc = m.mod_decl.mod_decl_loc }
                in
                Module.CallDef { call with call_decl }
              | symbol -> symbol
            in
            if not (Set.mem defined_symbols parent_symbol_ident) then
              (* case: parent_symbol should be inherited *)
              let parent_symbol =
                match parent_symbol with
                | CallDef call when not @@ Callable.is_abstract call ->
                  Logs.info (fun m -> m !"Making %{Ident} free." (Callable.to_ident call));
                  Module.CallDef (Callable.make_free call)
                | CallDef
                    ({ call_decl = { call_decl_kind = Lemma; _ }; _ } as call)
                  when Callable.is_abstract call
                       && not m.mod_decl.mod_decl_is_interface ->
                  let loc = m.mod_decl.mod_decl_loc in
                  let call =
                    {
                      Callable.call_decl = { call.call_decl with call_decl_is_auto = false };
                      call_def =
                        ProcDef { proc_body = Some (Stmt.mk_skip ~loc) };
                    }
                  in
                  let call =
                    if m.mod_decl.mod_decl_is_free
                    then Callable.make_free call
                    else call
                  in
                  annotate_error_msg (CallDef call)
                | _ -> annotate_error_msg parent_symbol
              in
              
              merge_defs
                (Module.SymbolDef parent_symbol :: merged, to_check, seen)
                (parent_mod_def, mod_def)
            else
              match mod_def with
              | Module.SymbolDef symbol :: mod_def ->
                  let symbol_ident = Symbol.to_name symbol in
                  if Set.mem seen symbol_ident then
                    (* case: symbol provides definition of another symbol that has already been seen earlier *)
                    merge_defs
                      (Module.SymbolDef symbol :: merged, to_check, seen)
                      (Module.SymbolDef parent_symbol :: parent_mod_def, mod_def)
                  else if Ident.(parent_symbol_ident = symbol_ident) then
                    (* case: symbol provides definition of parent_symbol *)
                    merge_defs
                      ( Module.SymbolDef symbol :: merged,
                        Map.add_exn to_check ~key:symbol_ident
                          ~data:parent_symbol,
                        seen )
                      (parent_mod_def, mod_def)
                  else if Set.mem defined_symbols parent_symbol_ident then
                    (* case: parent_symbol is defined later in mod_def *)
                    merge_defs
                      ( merged,
                        Map.add_exn to_check ~key:parent_symbol_ident
                          ~data:parent_symbol,
                        Set.add seen parent_symbol_ident )
                      (parent_mod_def, Module.SymbolDef symbol :: mod_def)
                  else
                    (* case: symbol is newly declared symbol *)
                    merge_defs
                      (Module.SymbolDef symbol :: merged, to_check, seen)
                      (Module.SymbolDef parent_symbol :: parent_mod_def, mod_def)
              | def :: mod_def ->
                  merge_defs
                    (def :: merged, to_check, seen)
                    (Module.SymbolDef parent_symbol :: parent_mod_def, mod_def)
              | [] -> assert false)
      in
      merge_defs
        ([], Map.empty (module Ident), Set.empty (module Ident))
        (parent_mod_def, mod_def)
    in

    (* Compute symbols that are inherited from parent interface, respectively, that need to be checked against the parent interface *)
    let* ( mod_decl_returns,
           mod_decl_interfaces,
           interface_ident,
           (merged_symbols, symbols_to_check) ) =
      let+ interface_opt =
        Rewriter.Option.map m.mod_decl.mod_decl_returns ~f:(fun mid ->
            Logs.debug (fun mm ->
                mm
                  !"Typing.process_module: module %{Ident}: checking return \
                    type %{QualIdent}"
                  (Symbol.to_name (ModDef m))
                  mid);
            let* qual_interface_ident, interface_symbol =
              Rewriter.resolve_and_find m.mod_decl.mod_decl_loc mid
            in
            let interface_symbol =
              Rewriter.Symbol.add_subst
                (qual_interface_ident, QualIdent.to_list mod_qual_ident)
                interface_symbol
            in

            let+ interface_symbol = Rewriter.Symbol.reify interface_symbol in
            Logs.debug (fun mm ->
                mm
                  !"Typing.process_module: %{Ident}: checking return type \
                    %{Symbol}: reified; \n\
                   \ qual_interface_ident: %{QualIdent} \n\
                   \ mid: %{QualIdent}"
                  (Symbol.to_name (ModDef m))
                  interface_symbol qual_interface_ident mid);
            (qual_interface_ident, mid, interface_symbol))
      in
      match interface_opt with
      | Some (qual_interface_ident, interface_ident, ModDef interface) ->
          ( Some qual_interface_ident,
            Set.add interface.mod_decl.mod_decl_interfaces qual_interface_ident,
            interface_ident,
            merge_defs qual_interface_ident interface.mod_def m.mod_def )
      | _ ->
          let mod_ident = QualIdent.from_ident m.mod_decl.mod_decl_name in
          let interfaces =
            if is_root then m.mod_decl.mod_decl_interfaces
            else Set.add m.mod_decl.mod_decl_interfaces mod_qual_ident
          in
          (None, interfaces, mod_ident, (m.mod_def, Map.empty (module Ident)))
    in

    (*let inherited_symbols = List.rev inherited_symbols in*)
    let mod_def = mod_def_formals @ merged_symbols in

    let* _ =
      Rewriter.List.map mod_def ~f:(function
        | Module.SymbolDef symbol -> Rewriter.declare_symbol symbol
        | Module.Import import -> Rewriter.import import)
    in

    (* Find rep type and add it to module declaration *)
    let mod_decl_rep =
      List.fold_left mod_def ~init:None ~f:(fun rep_type -> function
        | SymbolDef (TypeDef type_def) when type_def.type_def_rep ->
            Option.map_or_else
              ~m:(fun _ ->
                Error.syntax_error type_def.type_def_loc
                  (Printf.sprintf
                     !"Found more than one rep type in module %{Ident}"
                     m.mod_decl.mod_decl_name))
              ~e:(fun () -> Some type_def.type_def_name)
              () rep_type
        | _ -> rep_type)
    in

    (* Determine whether this module is an RA *)
    let _ =
      Set.iter mod_decl_interfaces ~f:(fun qid ->
          Logs.debug (fun m -> m !"%{QualIdent}" qid))
    in
    let* mod_decl_is_ra =
      Rewriter.List.exists (Set.to_list mod_decl_interfaces)
        ~f:(fun interface_ident ->
          let+ _qual_interface_ident, interface_symbol =
            Rewriter.resolve_and_find
              (QualIdent.to_loc interface_ident)
              interface_ident
          in
          Rewriter.Symbol.extract interface_symbol ~f:(fun _ -> function
            | Module.ModDef mod_def -> mod_def.mod_decl.mod_decl_is_ra
            | _ -> false))
    in
    let mod_decl_is_ra =
      mod_decl_is_ra
      || QualIdent.(mod_qual_ident = Ast.Predefs.lib_ra_mod_qual_ident)
    in

    (* Logs.debug (fun mm -> mm !"Typing.process_module: module %{Ident}: mod_decl_is_ra: %{Bool}" (Symbol.to_name (ModDef m)) mod_decl_is_ra); *)

    (* Add return type to module declaration *)
    let* mod_decl_formals =
      Rewriter.List.map m.mod_decl.mod_decl_formals ~f:(fun mod_inst ->
          let+ mod_inst_type =
            Rewriter.resolve mod_inst.mod_inst_loc mod_inst.mod_inst_type
          in
          { mod_inst with mod_inst_type })
    in

    let mod_decl =
      {
        m.mod_decl with
        mod_decl_rep;
        mod_decl_returns;
        mod_decl_formals;
        mod_decl_interfaces;
        mod_decl_is_ra;
      }
    in

    (* Check and rewrite all symbols *)
    let* mod_def = Rewriter.List.map merged_symbols ~f:process_instr in

    (* Check symbols against interface *)
    let+ _ =
      Rewriter.List.iter mod_def ~f:(function
        | SymbolDef symbol ->
            let ident = Symbol.to_name symbol in
            Map.find symbols_to_check ident
            |> Rewriter.Option.iter ~f:(fun orig_symbol ->
                   check_implements_symbol interface_ident symbol orig_symbol)
        | _ -> Rewriter.return ())
    in

    (* Check whether modules are indeed modules *)
    let _ =
      if not mod_decl.mod_decl_is_interface then
        List.iter mod_def ~f:(function
          | Import _ -> ()
          | SymbolDef symbol -> (
              match symbol with
              | TypeDef { type_def_expr = None; _ }
              | ModInst { mod_inst_def = None; _ }
              | VarDef { var_decl = { var_const = true; _ }; var_init = None }
              | CallDef { call_def = ProcDef { proc_body = None }; _ }
              | CallDef { call_def = FuncDef { func_body = None }; _ } ->
                  Error.type_error mod_decl.mod_decl_loc
                    (Printf.sprintf
                       !"Module %{Ident} must be declared as an interface. The \
                         %s %{Ident} is still abstract."
                       mod_decl.mod_decl_name (Symbol.kind symbol)
                       (Symbol.to_name symbol))
              | _ -> ()))
    in
    let _ =
      Logs.debug (fun mm ->
          mm !"Done with processing module %{Ident}" (Symbol.to_name (ModDef m)))
    in

    Module.{ mod_decl; mod_def }
end

let process_module ?(tbl = SymbolTbl.create ()) (m : Module.t) =
  assert (SymbolTbl.curr_is_root tbl);
  (* assert Ident.(m.mod_decl.mod_decl_name = QualIdent.to_ident (SymbolTbl.root_ident tbl)); *)
  let tbl, m =
    Rewriter.eval
      (fun st ->
        let st, _ = Rewriter.enter_module m st in
        let st, m = ProcessModule.process_module m st in
        let st, m = Rewriter.exit_module m st in
        (st, m))
      tbl
  in
  (tbl, m)

let process_symbol (symbol : Module.symbol) : Module.symbol Rewriter.t =
  let open Rewriter.Syntax in
  let* symbol =
    match symbol with
    | Module.TypeDef type_def -> ProcessModule.process_type_def type_def
    | Module.VarDef var_def -> ProcessModule.process_var var_def
    | Module.FieldDef field_def -> ProcessModule.process_field field_def
    | Module.ConstrDef _ | Module.DestrDef _ ->
        Rewriter.return
          symbol (* These should not occur directly in a module definition *)
    | Module.CallDef call_def -> ProcessCallable.process_callable call_def
    | Module.ModDef mod_def ->
        let* _ = Rewriter.enter_module mod_def
        and* mod_def = ProcessModule.process_module mod_def in
        let+ mod_def = Rewriter.exit_module mod_def in
        Module.ModDef mod_def
    | Module.ModInst mod_inst ->
        (* TODO: Implement checking for mod_inst too *)
        Rewriter.return symbol
  in

  let+ _ = Rewriter.set_symbol symbol in
  symbol
