(** Type checking of expressions. *)

open Base
open Ast
open Util
open Error
open TypingMonad
open TypingErrors

(** Whether the core's map lookup and update apply to an operand of type [typ]. *)
let is_core_indexable (typ : type_expr) : bool =
  match typ with Type.App ((Map | FinSet | Bot | Any), _, _) -> true | _ -> false

(** Whether [expr], an operand the core indexes, may have a type other than a map; only
    such operands are typed before a construct is offered to the extensions. *)
let may_have_non_map_type (expr : expr) : bool =
  match expr with
  | App
      ( ( Var _ | Read | DataDestr _ | TupleLookUp | MapLookUp | Ite | ExprExt _ | Union
        | Inter | Diff ),
        _,
        _ ) ->
      true
  | _ -> false

(** The operand that the updates [expr] are applied to, as in `m` of `m[i := a][j := b]`.
*)
let rec update_root (expr : expr) : expr =
  match expr with App (MapUpdate, base :: _, _) -> update_root base | _ -> expr

let set_checked_type (expr : expr) (given_typ_lb : type_expr) (given_typ_ub : type_expr)
    (expected_typ : type_expr) : expr t =
  let open Rewriter.Syntax in
  let expected_ghost = Type.is_ghost expected_typ in
  let+ given_typ_lb =
    try TypeExpr.expand_type_expr given_typ_lb
    with Msg msgs ->
      Error.fail_with
        (List.map msgs ~f:(fun (lbl, _loc, msg) -> (lbl, Expr.to_loc expr, msg)))
  and+ given_typ_ub = TypeExpr.expand_type_expr given_typ_ub
  and+ expected_typ = TypeExpr.expand_type_expr expected_typ
  and+ printers = Rewriter.current_printers
  and+ tbl = Rewriter.get_table in
  let _ =
    if
      (not @@ expected_ghost) && (Type.is_ghost given_typ_ub || Type.is_ghost given_typ_lb)
    then
      Error.type_error (Expr.to_loc expr)
        "This expression reads ghost state, so it can only be used inside a ghost block, \
         spec, or ghost-typed field"
  in
  let typ = Type.meet given_typ_ub expected_typ |> Type.set_ghost expected_ghost in
  if Type.subtype_of given_typ_lb typ then Expr.set_type expr typ
  else begin
    Logs.debug (fun m ->
        m
          "ExprTyping.set_checked_type: expr: %a;\n\
          \    given_typ_lb: %a\n\
          \    given_typ_ub: %a\n\
          \    expected_typ: %a"
          printers.pr_expr expr printers.pr_type given_typ_lb printers.pr_type
          given_typ_ub printers.pr_type expected_typ);
    type_mismatch_error_diagnosed tbl (Expr.to_loc expr) expected_typ given_typ_ub
  end

(** Infers and checks the type of [expr] against [expected_typ]. [allow_proc_call] permits
    a call of a procedure or lemma, which may occur only as the right-hand side of an
    assignment. *)
let rec check ?(allow_proc_call = false) (expr : expr) (expected_typ : type_expr) : expr t
    =
  let open Rewriter.Syntax in
  let* () =
    Rewriter.Logs.debug (fun printers m ->
        m "ExprTyping.check: %a; expected: %a is ghost: %b" printers.pr_expr expr
          printers.pr_type expected_typ (Type.is_ghost expected_typ))
  in
  match Expr.to_type_annot expr with
  | Some annot_typ ->
      (* `(e: T)`: checks `e` against the annotation `T`, then the result against
         [expected_typ]. *)
      let* annot_typ = TypeExpr.check annot_typ in
      let annot_typ = annot_typ |> Type.set_ghost_to expected_typ in
      let* e = check ~allow_proc_call (Expr.set_type_annot expr None) annot_typ in
      let actual_typ = Expr.to_type e in
      set_checked_type e actual_typ actual_typ expected_typ
  | None -> (
      match expr with
      | App (constr, expr_list, expr_attr) -> (
          let* claimed = claim_core_app constr expr_list expr_attr expected_typ in
          match claimed with
          | Some expr -> Rewriter.return expr
          | None -> (
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
                        ( Type.(mk_finset (Expr.to_loc expr) any),
                          Type.(mk_finset (Expr.to_loc expr) bot) )
                    | _ -> assert false
                  in
                  set_checked_type expr given_type_lb given_type_ub expected_typ
              | (Null | Real _ | Int _ | Bool _ | Empty), _expr_list ->
                  Error.type_error (Expr.to_loc expr)
                    (Expr.constr_to_string constr ^ " takes no arguments")
              (* Variables, fields, and call expressions *)
              | Var qual_ident, args_list -> (
                  let* resolved =
                    (* `M.foo` where `M` is an uninstantiated generic functor: try to solve
                 its type argument(s) from the call and rewrite to the instantiation. *)
                    ImplicitInstantiation.resolve_or_implicit_opt qual_ident
                      ~on_miss:(fun () ->
                        (* An unqualified name imported from an uninstantiated functor is
                           recovered from the import first. *)
                        let* imported = Rewriter.find_import_target qual_ident in
                        let candidate = Base.Option.value imported ~default:qual_ident in
                        ImplicitInstantiation.try_resolve_implicit_instantiation
                          ~check_expr:check ~claimed_location ~loc:(Expr.to_loc expr)
                          ~qual_ident:candidate ~arg_exprs:args_list ~expected_typ ())
                  in
                  match resolved with
                  | None ->
                      (* Unresolved. While speculating, this gives `Bot`, as an
                         underdetermined literal does, so that the enclosing call decides;
                         otherwise it is an unknown identifier. *)
                      let* speculative = is_speculative in
                      if speculative then
                        set_checked_type expr Type.bot Type.bot expected_typ
                      else
                        let* _ = Rewriter.resolve_and_find qual_ident in
                        Error.internal_error (Expr.to_loc expr)
                          "Rewriter.resolve_and_find unexpectedly succeeded after \
                           ImplicitInstantiation.resolve_or_implicit_opt failed"
                  | Some (qual_ident, symbol) -> (
                      let* symbol = Rewriter.Symbol.reify symbol in
                      match symbol with
                      | ConstrDef _constr ->
                          check
                            (App (DataConstr qual_ident, args_list, Expr.attr_of expr))
                            expected_typ
                      | CallDef callable ->
                          let callable_decl = Callable.to_decl callable in
                          let* _ =
                            match callable_decl.call_decl_kind with
                            | (Proc | Lemma) when not allow_proc_call ->
                                Error.type_error (Expr.to_loc expr)
                                  (Printf.sprintf
                                     !"%s %{Ident} can only be called as the right-hand \
                                       side of an assignment statement, e.g. `x := \
                                       %{Ident}(...)`. Assign its result to a variable \
                                       first if you need to use it in an expression"
                                     (match callable_decl.call_decl_kind with
                                     | Proc -> "Procedure"
                                     | _ -> "Lemma")
                                     callable_decl.call_decl_name
                                     callable_decl.call_decl_name)
                            | _ -> Rewriter.return ()
                          in
                          let* is_ghost_scope = Rewriter.is_ghost_scope in
                          let is_ghost_scope =
                            is_ghost_scope
                            ||
                            match callable_decl.call_decl_kind with
                            | Lemma | Pred | Invariant -> true
                            | Func -> expected_typ |> Type.is_ghost
                            | _ -> false
                          in
                          let* args_list =
                            check_args (Expr.to_loc expr) is_ghost_scope callable_decl
                              args_list
                          in
                          let* _ =
                            (* If this is an auto lemma, check that it is well-formed *)
                            if
                              callable.call_decl.call_decl_is_auto
                              &&
                              match callable_decl.call_decl_kind with
                              | Lemma -> true
                              | _ -> false
                            then begin
                              let+ _ =
                                Rewriter.List.iter
                                  (callable.call_decl.call_decl_precond
                                 @ callable.call_decl.call_decl_postcond) ~f:(fun spec ->
                                    let+ is_pure =
                                      lift (ProgUtils.is_expr_pure spec.spec_form)
                                    in
                                    if not is_pure then
                                      Error.type_error callable.call_decl.call_decl_loc
                                        (Printf.sprintf
                                           !"This specification of auto lemma %{Ident} \
                                             is not pure"
                                           callable.call_decl.call_decl_name))
                              in
                              ()
                            end
                            else Rewriter.return ()
                          in
                          let given_typ = Callable.return_type callable_decl in
                          let expr = Expr.App (Var qual_ident, args_list, expr_attr) in
                          set_checked_type expr given_typ given_typ expected_typ
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
                          set_checked_type expr given_typ given_typ expected_typ
                      | _ ->
                          Error.type_error (Expr.to_loc expr)
                            ("Expected a variable, field, or callable identifier, but \
                              found "
                            ^ QualIdent.to_string qual_ident)))
              (* Unary expressions *)
              | (Not | Uminus), [ expr_arg ] ->
                  let given_type_ub =
                    let ty =
                      match constr with
                      | Uminus -> Type.num
                      | Not -> Type.bool
                      | _ -> assert false
                    in
                    ty |> Type.set_ghost_to expected_typ
                  in
                  let* expr_arg = check expr_arg given_type_ub in
                  let given_type_lb = Expr.to_type expr_arg in
                  set_checked_type
                    (App (constr, [ expr_arg ], expr_attr))
                    given_type_lb given_type_lb expected_typ
              | (Not | Uminus), _expr_list ->
                  Error.type_error (Expr.to_loc expr)
                    (Expr.constr_to_string constr ^ " takes exactly one argument")
              (* Set operators, given their meaning by an extension, see [claim_core_app] *)
              | (Choose | Diff | Union | Inter | Subseteq), _ ->
                  Error.type_error (Expr.to_loc expr)
                    (Expr.constr_to_string constr ^ " is missing its arguments")
              (* Binary expressions *)
              | ( ( TupleLookUp | MapLookUp | Plus | Minus | Mult | Div | Mod | Gt | Lt
                  | Geq | Leq | And | Or | Impl | Elem | Eq ),
                  [ expr1; expr2 ] ) ->
                  (* infer and propagated expected type of expr1 *)
                  let expected_typ1 =
                    let ty =
                      match constr with
                      | TupleLookUp -> Type.(any)
                      | MapLookUp -> Type.(map bot expected_typ)
                      | Plus | Minus | Mult | Div | Mod | Gt | Lt | Geq | Leq -> Type.num
                      | And | Or -> Type.perm
                      | Impl -> Type.bool (* antecedent must be pure *)
                      | Elem | Eq -> Type.any
                      | _ -> assert false
                    in
                    ty |> Type.set_ghost_to expected_typ
                  in
                  let* expr1 = check expr1 expected_typ1 in
                  let typ1 = Expr.to_type expr1 in
                  (* infer and propagated expected type of expr2 *)
                  let expected_typ2 =
                    let ty =
                      match constr with
                      | TupleLookUp -> Type.int
                      | MapLookUp -> Type.map_dom typ1
                      | Plus | Minus | Mult | Div | Mod | Gt | Lt | Geq | Leq -> typ1
                      | Eq -> (
                          (* Widened, so that either side may be the finite set: the two sides
                     are then typed at their join below. *)
                          match typ1 with
                          | App (FinSet, [ elem ], _) -> Type.set_typed elem
                          | _ -> typ1)
                      | And | Or | Impl -> Type.perm
                      | Elem -> Type.(set_typed typ1)
                      | _ -> assert false
                    in
                    ty |> Type.set_ghost_to expected_typ
                  in
                  let* expr2 = check expr2 expected_typ2 in
                  let typ2 = Expr.to_type expr2 in

                  (* backpropagate typ2 to expr1 if needed *)
                  let expected_typ1 =
                    let ty =
                      match constr with
                      | TupleLookUp ->
                          let idx = Expr.to_int expr2 in
                          begin match typ1 with
                          | App (Prod, ts, _) when idx < List.length ts && idx >= 0 ->
                              typ1
                          | App (Prod, ts, _) ->
                              Error.type_error (Expr.to_loc expr2)
                                (Printf.sprintf
                                   !"Tuple index %d is out of bounds; %{Type} has %d \
                                     component(s)"
                                   idx typ1 (List.length ts))
                          | App _ ->
                              Error.type_error (Expr.to_loc expr1)
                                (Printf.sprintf
                                   !"Expected product type, but found %{Type}"
                                   typ1)
                          end
                      | MapLookUp -> Type.(map typ2 (Type.map_codom typ1))
                      | Plus | Minus | Mult | Div | Mod | Eq | Gt | Lt | Geq | Leq ->
                          Type.join typ1 typ2
                      | And | Or | Impl -> Type.perm
                      | Elem -> Type.set_elem typ2
                      | _ -> assert false
                    in
                    ty |> Type.set_ghost_to expected_typ
                  in
                  let* expr1 =
                    if Type.equal expected_typ1 typ1 then Rewriter.return expr1
                    else check expr1 expected_typ1
                  in

                  let expected_typ =
                    let ty =
                      if not @@ Type.is_any expected_typ then expected_typ
                      else
                        match constr with
                        | TupleLookUp -> Type.tuple_lookup typ1 (Expr.to_int expr2)
                        | MapLookUp -> Type.map_codom typ1
                        | Plus | Minus | Mult | Div | Mod -> Type.join typ1 typ2
                        | And | Or | Impl -> expected_typ
                        | Eq | Gt | Lt | Geq | Leq | Elem -> Type.bool
                        | _ -> assert false
                    in
                    ty |> Type.set_ghost_to expected_typ
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
                    | Plus | Minus | Mult | Div | Mod ->
                        let typ = expr1 |> Expr.to_type in
                        (typ, typ)
                    | And | Or | Impl ->
                        let typ = expr1 |> Expr.to_type in
                        (Type.join typ typ2, Type.join typ typ2)
                    | Elem | Eq | Gt | Lt | Geq | Leq -> (Type.bool, Type.bool)
                    | _ -> assert false
                  in
                  set_checked_type
                    (App (constr, [ expr1; expr2 ], expr_attr))
                    given_typ_lb given_typ_ub expected_typ
              | ( ( TupleLookUp | MapLookUp | Plus | Minus | Mult | Div | Mod | And | Or
                  | Impl | Elem | Eq | Gt | Lt | Geq | Leq ),
                  _expr_list ) ->
                  Error.type_error (Expr.to_loc expr)
                    (Expr.constr_to_string constr ^ " takes exactly two arguments")
              (* Ternary expressions *)
              | (Ite | MapUpdate), [ expr1; expr2; expr3 ] ->
                  (* infer and propagate expected type of expr1 *)
                  let expected_typ1 =
                    let ty =
                      match constr with
                      | Ite -> Type.bool
                      | MapUpdate -> Type.(map bot any)
                      | _ -> assert false
                    in
                    ty |> Type.set_ghost_to expected_typ
                  in
                  let* expr1 = check expr1 expected_typ1 in
                  let typ1 = Expr.to_type expr1 in
                  (* infer and propagate expected type of expr2 *)
                  let expected_typ2 =
                    let ty =
                      match constr with
                      | Ite -> expected_typ
                      | MapUpdate -> Type.map_dom typ1
                      | _ -> assert false
                    in
                    ty |> Type.set_ghost_to expected_typ
                  in
                  let* expr2 = check expr2 expected_typ2 in
                  let typ2 = Expr.to_type expr2 in
                  (* infer and propagate expected type of expr3 *)
                  let expected_typ3 =
                    let ty =
                      match constr with
                      | Ite -> expected_typ
                      | MapUpdate -> Type.map_codom typ1
                      | _ -> assert false
                    in
                    ty |> Type.set_ghost_to expected_typ
                  in
                  let* expr3 = check expr3 expected_typ3 in
                  let typ3 = Expr.to_type expr3 in
                  (* backpropagate typ3 to expr2 if needed *)
                  let expected_typ2 =
                    let ty =
                      match constr with
                      | Ite -> Type.join typ2 typ3
                      | MapUpdate -> typ2
                      | _ -> assert false
                    in
                    ty |> Type.set_ghost_to expected_typ
                  in
                  let* expr2 =
                    if Type.equal expected_typ2 typ2 then Rewriter.return expr2
                    else check expr2 expected_typ2
                  in
                  let typ2 = Expr.to_type expr2 in
                  (* backpropagate typ3 and typ2 to expr1 if needed *)
                  let expected_typ1 =
                    let ty =
                      match constr with
                      | Ite -> Type.bool
                      | MapUpdate -> Type.map typ2 typ3
                      | _ -> assert false
                    in
                    ty |> Type.set_ghost_to expected_typ
                  in
                  let* expr1 =
                    if Type.equal expected_typ1 typ1 then Rewriter.return expr1
                    else check expr1 expected_typ1
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
                  set_checked_type expr given_typ_lb given_typ_ub expected_typ
              | (Ite | MapUpdate), _expr_list ->
                  Error.type_error (Expr.to_loc expr)
                    (Expr.constr_to_string constr ^ " takes exactly three arguments")
              (* Ownership predicates *)
              | Own, arg_list ->
                  let* arg_list =
                    match arg_list with
                    | location :: rest ->
                        let+ location = claimed_location location in
                        location :: rest
                    | [] -> Rewriter.return []
                  in
                  let* expr1, expr2, expr3, expr4_opt =
                    match arg_list with
                    | (App
                         ( Read,
                           [ expr1; (App (Var qual_ident, [], expr_attr') as expr2) ],
                           _ ) as expr12)
                      :: expr3 :: expr4_opt -> begin
                        let* qual_ident, symbol = Rewriter.resolve_and_find qual_ident in
                        let+ symbol = Rewriter.Symbol.reify symbol in
                        match symbol with
                        | FieldDef _ -> (expr1, expr2, expr3, expr4_opt)
                        | _ -> (
                            match expr4_opt with
                            | expr41 :: expr4_opt -> (expr12, expr3, expr41, expr4_opt)
                            | _ ->
                                Error.type_error (Expr.to_loc expr12)
                                  "Expected field location")
                      end
                    | expr1
                      :: (App (Var qual_ident, [], expr_attr') as expr2)
                      :: expr3 :: expr4_opt ->
                        Rewriter.return (expr1, expr2, expr3, expr4_opt)
                    | _ ->
                        Error.type_error (Expr.to_loc expr)
                          (Expr.constr_to_string constr
                         ^ " takes either three or four arguments, and second argument \
                            is a field name")
                  in
                  let* expr1 = check expr1 (Type.ref |> Type.set_ghost_to expected_typ)
                  and* expr2 = check expr2 (Type.any |> Type.set_ghost_to expected_typ) in

                  let* field_type =
                    match expr2 with
                    | App (Var qual_ident, [], _) ->
                        let+ field_def = Rewriter.find_and_reify_field qual_ident in
                        field_def.field_type |> Type.field_val
                        |> Type.set_ghost_to expected_typ
                    | _ ->
                        Error.type_error (Expr.to_loc expr2) "Expected field identifier"
                  in
                  let* is_ra_type = lift (ProgUtils.is_ra_type field_type) in
                  let* expr3 = check expr3 field_type
                  (* Implicitely case-split on heap RA vs. other RA *)
                  and* expr4_opt =
                    match expr4_opt with
                    | [] ->
                        if not is_ra_type then
                          Rewriter.return [ Expr.mk_real ~loc:(Expr.to_loc expr) 1.0 ]
                        else Rewriter.return []
                    | [ e ] ->
                        if is_ra_type then
                          Error.type_error (Expr.to_loc e)
                            "'own(...)' for a field whose value is a resource algebra \
                             (RA) element does not take an extra fraction argument"
                        else
                          let+ e =
                            check e (Type.real |> Type.set_ghost_to expected_typ)
                          in
                          [ e ]
                    | _ ->
                        Error.type_error (Expr.to_loc expr)
                          "Too many arguments supplied to predicate 'own'"
                  in
                  (* Reconstruct and check expr *)
                  let expr =
                    Expr.App (Own, expr1 :: expr2 :: expr3 :: expr4_opt, expr_attr)
                  in
                  set_checked_type expr Type.perm Type.perm expected_typ
              | AUPred call_name, [ token; args_tuple ] ->
                  let loc = Expr.to_loc expr in
                  let* call_name, symbol = Rewriter.resolve_and_find call_name in

                  let args_list = Expr.unfold_tuple args_tuple in

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
                    let* token = check token (Type.atomic_token call_name) in
                    let* args_list =
                      check_args ~is_called:false loc true callable_decl args_list
                    in
                    let expr =
                      Expr.App
                        (AUPred call_name, [ token; Expr.mk_tuple args_list ], expr_attr)
                    in
                    set_checked_type expr Type.perm Type.perm expected_typ
              | AUPred _, _ ->
                  Error.type_error (Expr.to_loc expr)
                    "au<proc>() called with incorrect number of arguments. Expected: \
                     first argument: AtomicToken<proc>; second argument: tuple of proc \
                     args (or unit)"
              | AUPredCommit call_name, [ token; args_tuple; rets_tuple ] ->
                  let loc = Expr.to_loc expr in
                  let* call_name, symbol = Rewriter.resolve_and_find call_name in

                  let args_list = Expr.unfold_tuple args_tuple in

                  let* callable_decl =
                    let+ symbol = Rewriter.Symbol.reify symbol in
                    match symbol with
                    | CallDef callable
                      when Poly.(callable.call_decl.call_decl_kind = Proc) ->
                        callable.call_decl
                    | _ -> Error.type_error loc "Expected procedure identifier"
                  in

                  if not (Callable.is_atomic callable_decl) then
                    Error.type_error loc "Expected procedure with atomic specification"
                  else
                    let* token = check token (Type.atomic_token call_name) in
                    let* args_list =
                      check_args ~is_called:false loc true callable_decl args_list
                    in
                    let* rets_tuple =
                      check rets_tuple
                        (Type.mk_prod loc
                           (List.map callable_decl.call_decl_returns ~f:(fun v ->
                                v.var_type))
                        |> Type.set_ghost true)
                    in
                    let expr =
                      Expr.App
                        ( AUPredCommit call_name,
                          [ token; Expr.mk_tuple args_list; rets_tuple ],
                          expr_attr )
                    in
                    set_checked_type expr Type.perm Type.perm expected_typ
              | AUPredCommit _, _ ->
                  Error.type_error (Expr.to_loc expr)
                    "auCommit<proc>() called with incorrect number of arguments. \
                     Expected: first argument: AtomicToken<proc>; second argument: tuple \
                     of prog args (or unit); third argument: tuple of proc ret vals (or \
                     unit)"
              (* Data constructor expressions *)
              | DataConstr constr_ident, args_list ->
                  let loc = QualIdent.to_loc constr_ident in
                  let* constr_decl =
                    let* symbol = Rewriter.find constr_ident in
                    let+ symbol = Rewriter.Symbol.reify symbol in
                    match symbol with
                    | ConstrDef constr -> constr
                    | _ -> Error.type_error loc "Expected data constructor"
                  in
                  let constr_arg_types_list =
                    List.map constr_decl.constr_args ~f:(fun var_decl ->
                        var_decl.var_type |> Type.set_ghost_to expected_typ)
                  in
                  let* maybe_args_list =
                    Rewriter.List.map2 args_list constr_arg_types_list
                      ~f:(fun expr tp_expr -> check expr tp_expr)
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
                  set_checked_type expr given_typ given_typ expected_typ
              (* Data destructor expressions *)
              | DataDestr destr_qual_ident, [ expr1 ] ->
                  let loc = QualIdent.to_loc destr_qual_ident in
                  let* destr_qual_ident, destr =
                    let* destr_qual_ident, symbol =
                      Rewriter.resolve_and_find destr_qual_ident
                    in
                    let+ symbol = Rewriter.Symbol.reify symbol in
                    match symbol with
                    | DestrDef destr -> (destr_qual_ident, destr)
                    | _tp_env -> Error.type_error loc "Expected data destructor"
                  in
                  let* expr1 =
                    check expr1 (destr.destr_arg |> Type.set_ghost_to expected_typ)
                  in
                  let given_typ = destr.destr_return_type in
                  let expr =
                    Expr.App (DataDestr destr_qual_ident, [ expr1 ], expr_attr)
                  in
                  set_checked_type expr given_typ given_typ expected_typ
              | DataDestr _, _ ->
                  Error.type_error (Expr.to_loc expr)
                    (Expr.constr_to_string constr ^ " takes exactly one argument")
              (* Read expressions *)
              | Read, [ expr1; App (Var field_ident, [], expr_attr') ] -> (
                  let* qual_ident, symbol =
                    (* `e.M.value` for an uninstantiated functor `M`: inferred from the
                       type of `e` (see
                       [ImplicitInstantiation.try_resolve_implicit_instantiation_destr]).
                       An unqualified destructor imported from one is recovered from the
                       import first, as in the [Var] case. *)
                    ImplicitInstantiation.resolve_or_implicit field_ident
                      ~on_miss:(fun () ->
                        let* imported = Rewriter.find_import_target field_ident in
                        let candidate = Base.Option.value imported ~default:field_ident in
                        let* peeked_expr1 =
                          check expr1 (Type.any |> Type.set_ghost_to expected_typ)
                        in
                        ImplicitInstantiation.try_resolve_implicit_instantiation_destr
                          ~field_ident:candidate ~arg_typ:(Expr.to_type peeked_expr1))
                  in
                  let* symbol = Rewriter.Symbol.reify symbol in
                  match symbol with
                  | DestrDef _ ->
                      check
                        (App (DataDestr qual_ident, [ expr1 ], expr_attr))
                        expected_typ
                  | FieldDef _ ->
                      Error.type_error (Expr.to_loc expr)
                        (Printf.sprintf
                           !"Cannot read field %{QualIdent} in this context"
                           field_ident)
                  | _ ->
                      Error.type_error (Expr.to_loc expr)
                        (Printf.sprintf
                           !"Expected destructor identifier, but found %s %{QualIdent}"
                           (Symbol.kind symbol) qual_ident))
              | Read, _expr_list ->
                  Error.type_error (Expr.to_loc expr)
                    (Expr.constr_to_string constr ^ " takes exactly two arguments")
              (* Set enumeration expressions *)
              | Setenum, [] -> check (App (Empty, [], expr_attr)) expected_typ
              | Setenum, member_expr_list ->
                  (* TODO: make type inference for member_expr_list more precise by using expected_typ *)
                  let* member_expr_list, elem_typ =
                    Rewriter.List.fold_right member_expr_list
                      ~f:(fun mexpr (member_expr_list, elem_typ) ->
                        let+ mexpr =
                          check mexpr (elem_typ |> Type.set_ghost_to expected_typ)
                        in
                        (mexpr :: member_expr_list, Expr.to_type mexpr))
                      ~init:([], Type.any)
                  in
                  let given_typ = Type.finset_typed elem_typ in
                  let expr = Expr.App (Setenum, member_expr_list, expr_attr) in
                  set_checked_type expr given_typ given_typ expected_typ
              (* Tuple expressions *)
              | Tuple, elem_expr_list ->
                  let typed_elem_expr_list =
                    match expected_typ with
                    | App (Prod, ts, _) -> (
                        List.zip elem_expr_list ts |> function
                        | Ok res -> res
                        | _ ->
                            tuple_arg_mismatch_error (Expr.to_loc expr) (List.length ts))
                    | _ ->
                        List.map
                          ~f:(fun e -> (e, Type.any |> Type.set_ghost_to expected_typ))
                          elem_expr_list
                  in
                  let* elem_expr_list, elem_types =
                    Rewriter.List.fold_right typed_elem_expr_list
                      ~f:(fun (mexpr, mtyp) (elem_expr_list, elem_types) ->
                        let+ mexpr = check mexpr mtyp in
                        (mexpr :: elem_expr_list, Expr.to_type mexpr :: elem_types))
                      ~init:([], [])
                  in
                  let given_typ = Type.mk_prod (Expr.to_loc expr) elem_types in
                  let expr = Expr.App (Tuple, elem_expr_list, expr_attr) in
                  set_checked_type expr given_typ given_typ expected_typ
              | ExprExt expr_ext, expr_list ->
                  let* ext_hooks = Rewriter.current_ext_hooks in
                  (* The extension's own operands are typed as speculatively as the construct. *)
                  let* depth = speculative_depth in
                  lift
                    (ext_hooks.type_check_expr expr_ext expr_list expr_attr expected_typ
                       {
                         set_checked_type =
                           (fun e lb ub exp ->
                             run_typing_at depth (set_checked_type e lb ub exp));
                         check_expr = (fun e exp -> run_typing_at depth (check e exp));
                         type_mismatch_error;
                         expand_type_expr =
                           (fun tp -> run_typing (TypeExpr.expand_type_expr tp));
                       })))
      | Binder (binder, var_decl_list, trgs, inner_expr, expr_attr) -> (
          let* var_decl_list =
            Rewriter.List.map var_decl_list ~f:(fun var_decl ->
                TypeExpr.check_var_decl var_decl)
          in
          let* _ = Rewriter.add_locals var_decl_list in

          match binder with
          | Forall | Exists ->
              let* inner_expr = check inner_expr expected_typ in
              let* trgs =
                Rewriter.List.map trgs ~f:(fun trg ->
                    Rewriter.List.map trg ~f:(fun expr ->
                        check expr (Type.any |> Type.set_ghost true)))
              in

              (* TODO: Add additional checks for triggers *)
              let inner_typ = Expr.to_type inner_expr in
              let expr =
                Expr.Binder (binder, var_decl_list, trgs, inner_expr, expr_attr)
              in
              set_checked_type expr Type.bool
                (Type.perm |> Type.set_ghost_to expected_typ)
                inner_typ
          | Compr ->
              let var_decl =
                match var_decl_list with
                | [ v ] -> v
                | _ ->
                    Error.type_error (Expr.to_loc expr)
                      "Map/set comprehensions can only quantify over one variable"
              in

              let inner_expr_expected_typ =
                let ty =
                  match expected_typ with App (Map, [ _; tp ], _) -> tp | _ -> Type.any
                in
                ty |> Type.set_ghost_to expected_typ
              in

              let* inner_expr = check inner_expr inner_expr_expected_typ in
              let inner_expr_type = Expr.to_type inner_expr in

              let expr_typ =
                if Type.equal inner_expr_type Type.bool then
                  Type.mk_set var_decl.var_loc var_decl.var_type
                else Type.mk_map var_decl.var_loc var_decl.var_type inner_expr_type
              in

              let expr =
                Expr.Binder (binder, var_decl_list, trgs, inner_expr, expr_attr)
              in
              set_checked_type expr expr_typ expr_typ expected_typ))

(* end of check *)

(* [expr1], an operand the core indexes, typed against [expected_typ] if its type is
     one the core's lookup and update do not apply to. *)
and non_core_indexable (expr1 : expr) (expected_typ : type_expr) : expr option t =
  let open Rewriter.Syntax in
  let typed_if_not_core expr =
    if not (may_have_non_map_type expr) then Rewriter.return None
    else
      let* expr = speculatively (check expr expected_typ) in
      let+ typ = TypeExpr.expand_type_expr (Expr.to_type expr) in
      if is_core_indexable typ then None else Some expr
  in
  match expr1 with
  | App (MapUpdate, _, _) -> (
      (* The chain is typed only if the operand it updates is not a map, which keeps
           chains such as `m[i := a][j := b]` from being typed at every link. *)
      let* root = typed_if_not_core (update_root expr1) in
      match root with
      | None -> Rewriter.return None
      | Some _ -> typed_if_not_core_update expr1 expected_typ)
  | _ -> typed_if_not_core expr1

(* [expr1], an update chain on an operand that is not a map, typed. *)
and typed_if_not_core_update (expr1 : expr) (expected_typ : type_expr) : expr option t =
  let open Rewriter.Syntax in
  let* expr1 = speculatively (check expr1 expected_typ) in
  let+ typ1 = TypeExpr.expand_type_expr (Expr.to_type expr1) in
  if is_core_indexable typ1 then None else Some expr1

(* [expr], found where a field location `x.f` is expected, as the location an
     extension claims it denotes; otherwise [expr] itself. *)
and claimed_location (expr : expr) : expr t =
  let open Rewriter.Syntax in
  match expr with
  | App (MapLookUp, [ base; index ], expr_attr) -> (
      let* base = non_core_indexable base (Type.any |> Type.set_ghost true) in
      match base with
      | None -> Rewriter.return expr
      | Some base -> (
          let* ext_hooks = Rewriter.current_ext_hooks in
          let+ claim =
            lift (ext_hooks.claim_location (App (MapLookUp, [ base; index ], expr_attr)))
          in
          match claim with
          | None -> expr
          | Some (ref_expr, field) ->
              let field_expr =
                Expr.mk_app ~loc:(Expr.to_loc expr) ~typ:Type.any (Var field) []
              in
              Expr.App (Read, [ ref_expr; field_expr ], expr_attr)))
  | _ -> Rewriter.return expr

(* Offers to the extensions a map lookup or update, or a membership `e in c`, whose map
     or set operand has a type the core's rule does not apply to, and the set operators. *)
and claim_core_app (constr : Expr.constr) (expr_list : expr list)
    (expr_attr : Expr.expr_attr) (expected_typ : type_expr) : expr option t =
  let open Rewriter.Syntax in
  let non_core_indexable expr1 =
    non_core_indexable expr1 (Type.any |> Type.set_ghost_to expected_typ)
  in
  let offer (args : expr list) : expr option t =
    let* ext_hooks = Rewriter.current_ext_hooks in
    let* claim = lift (ext_hooks.claim_expr constr args expr_attr) in
    match claim with
    | None -> Rewriter.return None
    | Some (expr_ext, args) ->
        let+ expr = check (App (ExprExt expr_ext, args, expr_attr)) expected_typ in
        Some expr
  in
  match (constr, expr_list) with
  | (MapLookUp | MapUpdate), expr1 :: rest -> (
      let* expr1 = non_core_indexable expr1 in
      match expr1 with None -> Rewriter.return None | Some expr1 -> offer (expr1 :: rest))
  | Elem, [ elem; container ] -> (
      let* container = non_core_indexable container in
      match container with
      | None -> Rewriter.return None
      | Some container -> offer [ elem; container ])
  | (Union | Inter | Diff | Subseteq | Choose), _ :: _ -> (
      (* The core gives the set operators no meaning of their own. *)
      let* args =
        Rewriter.List.map expr_list ~f:(fun e ->
            speculatively (check e (Type.any |> Type.set_ghost_to expected_typ)))
      in
      let* claimed = offer args in
      match claimed with
      | Some expr -> Rewriter.return (Some expr)
      | None ->
          let culprit =
            List.find args ~f:(fun e -> not (Type.is_set (Expr.to_type e)))
            |> Option.value ~default:(List.hd_exn args)
          in
          type_mismatch_error (Expr.to_loc culprit)
            Type.(set_typed bot)
            (Expr.to_type culprit))
  | _ -> Rewriter.return None

and check_args ?(is_called = true) loc is_ghost_scope callable_decl args_list =
  let open Rewriter.Syntax in
  let callable_formals =
    match callable_decl.call_decl_kind with
    | Proc when is_ghost_scope && is_called ->
        Error.type_error loc "Cannot call procedure in ghost context"
    | Pred | Invariant ->
        callable_decl.call_decl_formals @ callable_decl.call_decl_returns
    | _ -> callable_decl.call_decl_formals
  in
  let is_ghost_call =
    match callable_decl.call_decl_kind with
    | Pred | Invariant | Lemma -> true
    | _ -> false
  in

  let* () =
    Rewriter.Logs.debug (fun printers m ->
        m "ExprTyping.check_args: args_list=%a"
          (Util.Print.pr_list_comma printers.pr_expr)
          args_list)
  in

  (* Check if too few arguments given. *)
  let _ =
    List.drop callable_formals (List.length args_list)
    |> List.find ~f:(fun var_decl -> not @@ var_decl.Type.var_implicit)
    |> Option.iter ~f:(fun decl ->
        Error.type_error loc
        @@ Printf.sprintf
             !"Explicit argument %s is missing in this call to %{Ident}"
             (Ident.name decl.Type.var_name)
             callable_decl.call_decl_name)
  in

  (* A location parameter may be given as `x.f`, with the field the callee declares; `x`
     is passed. *)
  let* args_list =
    let locs = callable_decl.call_decl_loc_params in
    if List.is_empty locs then Rewriter.return args_list
    else
      Rewriter.List.map
        (List.mapi args_list ~f:(fun i a -> (i, a)))
        ~f:(fun (i, arg) ->
          match List.nth locs i with
          | None -> Rewriter.return arg
          | Some declared_field -> (
              let* arg = claimed_location arg in
              match arg with
              | Expr.App (Read, [ ref_expr; App (Var field, [], _) ], _) ->
                  let* field = Rewriter.resolve field in
                  let* declared_field = Rewriter.resolve declared_field in
                  if QualIdent.equal field declared_field then Rewriter.return ref_expr
                  else
                    Error.type_error (Expr.to_loc arg)
                      (Printf.sprintf
                         !"%{Ident} operates on field %{QualIdent} here, but this \
                           argument names %{QualIdent}"
                         callable_decl.call_decl_name declared_field field)
              | _ -> Rewriter.return arg))
  in
  let provided_formals = List.take callable_formals (List.length args_list) in
  let explicit_formal_types =
    List.map provided_formals ~f:(fun var_decl -> var_decl.Type.var_type)
  in
  let* _ = Rewriter.enter_ghost (is_ghost_call || is_ghost_scope) in
  match%bind
    Rewriter.List.map2 args_list explicit_formal_types ~f:(fun expr tp_expr ->
        check expr
          (tp_expr
          |> Type.set_ghost (Type.is_ghost tp_expr || is_ghost_call || is_ghost_scope)))
  with
  | Ok args_list ->
      let+ _ = Rewriter.exit_ghost in
      args_list
  | Unequal_lengths ->
      (* Catches if too many args given. *)
      Error.type_error loc
      @@ Printf.sprintf "Too many arguments passed to %s"
           (Ident.to_string callable_decl.call_decl_name)

and check_returns loc ~is_ghost_scope ~is_call callable_decl returns_list =
  let open Rewriter.Syntax in
  let callable_returns = callable_decl.Callable.call_decl_returns in
  let is_ghost_call =
    match callable_decl.call_decl_kind with
    | Pred | Invariant | Lemma -> true
    | _ -> false
  in

  let* () =
    Rewriter.Logs.debug (fun printers m ->
        m "ExprTyping.check_returns: callable=%a; returns_list=[%a]" Ident.pr
          callable_decl.call_decl_name printers.pr_expr_list returns_list)
  in

  (* Check if too few returns given. *)
  let _ =
    let num_found = List.length returns_list in
    let num_expected = List.length callable_returns in
    if not (num_found = num_expected) then
      Error.type_error loc
      @@ Printf.sprintf
           !"%s has %d return parameter(s), but found %d return variable(s)"
           (callable_decl.call_decl_name |> Ident.to_string)
           num_expected num_found
  in

  let provided_returns = List.take callable_returns (List.length returns_list) in
  match%bind
    Rewriter.List.map2 returns_list provided_returns ~f:(fun expr var_decl ->
        let is_ghost =
          (if is_call then Type.is_ghost (expr |> Expr.to_type)
           else Type.is_ghost var_decl.Type.var_type)
          || is_ghost_call || is_ghost_scope
        in
        let tp_expr = var_decl.Type.var_type |> Type.set_ghost is_ghost in
        let+ expr = check expr tp_expr in
        expr)
  with
  | Ok returns_list -> Rewriter.return returns_list
  | Unequal_lengths ->
      (* Catches if too many return values given. *)
      Error.type_error loc
      @@ Printf.sprintf "Too many values returned for %s"
           (Ident.to_string callable_decl.call_decl_name)
