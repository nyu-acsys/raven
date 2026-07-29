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

(** Best-effort diagnostic for the common case behind a confusing "expected X but
    found Y" where X and Y turn out to be two different names for the same
    underlying module: their canonical declaration site
    ([SymbolTbl.resolve_and_find]'s first, alias-independent component) and
    instantiation-argument substitution agree, even though the identifiers used to
    reach them differ. Purely read-only -- never changes what type-checks, only
    what the error, if any, explains. *)
let explain_module_identity_mismatch (tbl : SymbolTbl.t) (exp_ty : type_expr)
    (fnd_ty : type_expr) : string option =
  match (exp_ty, fnd_ty) with
  | App (Var exp_qi, [], _), App (Var fnd_qi, [], _)
    when QualIdent.(exp_qi <> fnd_qi) -> (
      match
        ( SymbolTbl.resolve_and_find exp_qi tbl,
          SymbolTbl.resolve_and_find fnd_qi tbl )
      with
      | ( Some (exp_alias, _, _, (_, _, exp_subst)),
          Some (fnd_alias, _, _, (_, _, fnd_subst)) )
        when QualIdent.(exp_alias = fnd_alias) -> (
          (* [exp_alias]/[fnd_alias] name the physical declaration site both types
             trace back to (e.g. a rep type's own qualified name). Its owning
             module tells us whether any *real* type arguments could be
             involved: if it has no formals, every difference between
             [exp_subst] and [fnd_subst] is a structural rename picked up while
             chasing through aliases, not a semantic one, and the two types are
             genuinely the same. If it does have formals, we only know that for
             sure when both sides bind every formal to the same argument. *)
          let owning_module = QualIdent.pop exp_alias in
          match Map.find tbl.tbl_symbols owning_module with
          | Some (Module.ModDef { mod_decl = { mod_decl_formals = []; _ }; _ }) ->
              Some
                (Printf.sprintf
                   !"%{QualIdent} and %{QualIdent} are two different names for \
                     the same module (%{QualIdent}). Raven does not currently \
                     recognize their members as the same type -- use one name \
                     consistently wherever this type must match"
                   exp_qi fnd_qi owning_module)
          | Some (Module.ModDef { mod_decl = { mod_decl_formals; _ }; _ })
            when not (List.is_empty mod_decl_formals) ->
              let binding subst (formal : Module.module_inst) =
                let key = QualIdent.append owning_module formal.mod_inst_name in
                List.Assoc.find subst key ~equal:QualIdent.equal
              in
              let same_args =
                List.for_all mod_decl_formals ~f:(fun formal ->
                    match (binding exp_subst formal, binding fnd_subst formal) with
                    | Some a, Some b -> List.equal Ident.equal a b
                    | None, None -> true
                    | _ -> false)
              in
              if same_args then
                Some
                  (Printf.sprintf
                     !"%{QualIdent} and %{QualIdent} come from two separate \
                       instantiations of %{QualIdent} with the same arguments. \
                       Module instantiation is generative: each instantiation \
                       site produces its own distinct type, even when the \
                       arguments are identical. Bind a single instantiation \
                       explicitly and reuse it from both places, e.g. `module \
                       Shared = %{QualIdent}[...]`"
                     exp_qi fnd_qi owning_module owning_module)
              else None
          | _ -> None)
      | _ -> None)
  | _ -> None

(** Like [type_mismatch_error], but first tries
    [explain_module_identity_mismatch] and appends its explanation, if any. *)
let type_mismatch_error_diagnosed tbl loc exp_ty fnd_ty =
  match explain_module_identity_mismatch tbl exp_ty fnd_ty with
  | None -> type_mismatch_error loc exp_ty fnd_ty
  | Some explanation ->
      Error.type_error loc
        (Printf.sprintf
           !"Expected an expression of type\n\
            \  %{Type}\n\
             but found an expression of type\n\
            \  %{Type}.\n\n\
             %s"
           exp_ty fnd_ty explanation)

let number_to_string kind d =
  if d = 1 then Printf.sprintf "one %s" kind else Printf.sprintf "%d %ss" d kind

let tuple_arg_mismatch_error loc expected =
  Error.type_error loc
    (Printf.sprintf "Expected tuple with %s" (number_to_string "component" expected))

let arg_mismatch_error kind loc typ_constr expected =
  Error.type_error loc
    (Printf.sprintf "%s %s expects %s" kind (Type.to_name typ_constr)
       (number_to_string "argument" expected))

let param_mismatch_error kind loc id expected =
  Error.type_error loc
    (Printf.sprintf "%s %s expects %s" kind id (number_to_string "parameter" expected))

let unexpected_functor_error loc =
  Error.type_error loc
    "A functor can only be instantiated as the definition of a module (e.g. 'module M = F[...]'), not used as a type or value here"

module ProcessTypeExpr = struct
  let rec process_type_expr (tp_expr : type_expr) : type_expr Rewriter.t =
    let open Type in
    let open Rewriter.Syntax in
    match tp_expr with
    | App (Var qual_ident, [], tp_attr) -> (
        let+ fully_qualified_qual_ident, symbol =
          Rewriter.resolve_and_find qual_ident
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
        | _ -> Error.type_error tp_attr.type_loc "Expected type identifier")
    | App (Var qual_ident, (_ :: _ as tp_args), tp_attr) -> (
        (* `M[T1,...,Tn]`: if `M` is a functor with rep-typed formals, implicitly
           instantiate it (see `ProgUtils.instantiate_type_functor`) and resolve to the
           instantiation's rep type. Anything else is still rejected, as before. *)
        let* generic_functor = ProgUtils.resolve_generic_functor qual_ident in
        match generic_functor with
        | None -> unexpected_functor_error tp_attr.type_loc
        | Some (fully_qualified_qual_ident, m) ->
            if
              not
                (Int.equal (List.length tp_args) (List.length m.mod_decl.mod_decl_formals))
            then
              arg_mismatch_error "Module" tp_attr.type_loc (Type.Var qual_ident)
                (List.length m.mod_decl.mod_decl_formals)
            else
              let* tp_args = Rewriter.List.map tp_args ~f:process_type_expr in
              let* inst_qual_ident =
                ProgUtils.instantiate_type_functor ~loc:tp_attr.type_loc
                  ~f:!(Rewriter.process_symbol_ref)
                  ~functor_qual_ident:fully_qualified_qual_ident
                  ~functor_mod_decl:m.mod_decl tp_args
              in
              (match m.mod_decl.mod_decl_rep with
              | None ->
                  Error.type_error tp_attr.type_loc
                    ("Module "
                    ^ QualIdent.to_string qual_ident
                    ^ " does not have a rep type. It cannot be used in a context \
                       expecting a type")
              | Some rep_ident ->
                  Rewriter.return
                    (App
                       ( Var (QualIdent.append inst_qual_ident rep_ident),
                         [],
                         tp_attr ))))
    | App ((Fld as constr), tp_list, tp_attr) -> (
        match tp_list with
        | [ tp_arg ] ->
            let+ tp_arg' = process_type_expr tp_arg in
            App (constr, [ tp_arg' ], tp_attr)
        | _ -> arg_mismatch_error "Constructor" (Type.to_loc tp_expr) constr 1)
    | App (Map, tp_list, tp_attr) -> (
        match tp_list with
        | [ tp1; tp2 ] ->
            let+ tp1 = process_type_expr tp1 and+ tp2 = process_type_expr tp2 in
            App (Map, [ tp1; tp2 ], tp_attr)
        | _ -> arg_mismatch_error "Type" (Type.to_loc tp_expr) Map 2)
    | App (Data _, _tp_list, _tp_attr) ->
        (* The parser should prevent this from happening. *)
        Error.internal_error (Type.to_loc tp_expr)
          "Data types can only be defined as new types, not used inline"
    | App (Prod, tp_list, tp_attr) ->
        let+ tp_list = Rewriter.List.map tp_list ~f:process_type_expr in
        App (Prod, tp_list, tp_attr)
    | App (AtomicToken qid, [], tp_attr) ->
      let+ qid = Rewriter.resolve qid in
      App (AtomicToken qid, [], tp_attr)
    | App (TypeExt type_ext, tp_args, tp_attr) ->
      let* ext_hooks = Rewriter.current_ext_hooks in
      ext_hooks.type_check_type_expr type_ext tp_args tp_attr { process_type_expr }
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
              Rewriter.resolve_and_find qual_iden
            in
            let* qual_ident_def =
              Rewriter.Symbol.reify_type_def (Type.to_loc tp_expr) symbol
            in
            match qual_ident_def with
            | None ->
                Rewriter.return
                @@ (Type.App (Var qual_ident, tp_expr_list, tp_attr) |> Type.set_ghost_to tp_expr)
            | Some (App (Data _, _, _)) ->
                Rewriter.return
                @@ (Type.App (Var qual_ident, tp_expr_list, tp_attr) |> Type.set_ghost_to tp_expr)
            | Some tp_expr1 ->
              let+ exp_typ = expand_type_expr tp_expr1 in
              exp_typ |> Type.set_ghost_to tp_expr)
        | Var _, (_ :: _) ->
            (* `M[T1,...,Tn]` can reach here un-normalized via a self-referential
               lookup (e.g. a recursive call reading back its own declared type).
               Route through process_type_expr first, then keep expanding. *)
            let* tp_expr = process_type_expr tp_expr in
            expand_type_expr tp_expr
        | AtomicToken callable_qid, [] ->
          let+ callable_qid = Rewriter.resolve callable_qid in
          Type.App (AtomicToken callable_qid, [], tp_attr) |> Type.set_ghost_to tp_expr
        | AtomicToken _, _ ->
          unexpected_functor_error tp_attr.type_loc
        | _ ->
            let+ expanded_tp_expr_list =
              Rewriter.List.map tp_expr_list ~f:expand_type_expr
            in
            Type.App (constr, expanded_tp_expr_list, tp_attr) |> Type.set_ghost_to tp_expr)

  let process_var_decl (var_decl : var_decl) : var_decl Rewriter.t =
    let open Rewriter.Syntax in
    let* var_type = process_type_expr var_decl.var_type in
    let+ var_type = expand_type_expr var_type in
    { var_decl with var_type }
end

module ProcessExpr = struct
(* module ProcessExpr = struct *)
  let check_and_set (expr : expr) (given_typ_lb : type_expr)
      (given_typ_ub : type_expr) (expected_typ : type_expr) : expr Rewriter.t =
    let open Rewriter.Syntax in
    let expected_ghost = Type.is_ghost expected_typ in
    let+ given_typ_lb =
      try ProcessTypeExpr.expand_type_expr given_typ_lb
      with Msg msgs ->
        Error.fail_with
          (List.map msgs ~f:(fun (lbl, _loc, msg) -> (lbl, Expr.to_loc expr, msg)))
    and+ given_typ_ub = ProcessTypeExpr.expand_type_expr given_typ_ub
    and+ expected_typ = ProcessTypeExpr.expand_type_expr expected_typ
    and+ printers = Rewriter.current_printers
    and+ tbl = Rewriter.get_table in
    let _ =
      if not @@ expected_ghost && (Type.is_ghost given_typ_ub || Type.is_ghost given_typ_lb) then
        let _ = Logs.debug (fun m -> m "Failed with %a" printers.pr_expr expr) in
        Error.type_error (Expr.to_loc expr)
          "This expression reads ghost state, so it can only be used inside a ghost block, spec, or ghost-typed field"
    in
    let typ = Type.meet given_typ_ub expected_typ |> Type.set_ghost expected_ghost in
    if Type.subtype_of given_typ_lb typ then Expr.set_type expr typ
    else begin
      Logs.debug (fun m ->
          m "Frontend.typing.check_and_set: expr: %a;
    given_typ_lb: %a
    given_typ_ub: %a
    expected_typ: %a"
            printers.pr_expr expr
            printers.pr_type given_typ_lb
            printers.pr_type given_typ_ub
            printers.pr_type expected_typ
        );
      type_mismatch_error_diagnosed tbl (Expr.to_loc expr) expected_typ given_typ_ub
    end

  (** Infer and check type of [expr] subject to typing environment [tbl] and expected type [expected_typ].
      [allow_proc_call] permits [expr] itself to be a call to a procedure or lemma (as opposed to a
      function/predicate/invariant). This is only ever true for the top-level right-hand side of an
      assignment statement of the form [x1, ..., xn := p(e1, ..., em)] -- procedure/lemma calls are
      statements, not pure expressions, and cannot be embedded anywhere else (e.g. as an argument
      to another call, inside a return statement, or combined with other operators). *)
  let rec process_expr ?(allow_proc_call = false) (expr : expr) (expected_typ : type_expr) : expr Rewriter.t
    =
    let open Rewriter.Syntax in
    let* () = Rewriter.Logs.debug (fun printers m -> m "process_expr: %a; expected: %a is ghost: %b" printers.pr_expr expr printers.pr_type expected_typ (Type.is_ghost expected_typ)) in
    match Expr.to_type_annot expr with
    | Some annot_typ ->
        (* `(e: T)`: check `e` against the user's annotation `T` (which disambiguates
           an otherwise-underdetermined `e`, e.g. `({||}: Set[Int])`), then check that
           the resulting type is still consistent with the surrounding context
           [expected_typ] -- the annotation is never taken for granted. *)
        let* annot_typ = ProcessTypeExpr.process_type_expr annot_typ in
        let annot_typ = annot_typ |> Type.set_ghost_to expected_typ in
        let* e = process_expr ~allow_proc_call (Expr.set_type_annot expr None) annot_typ in
        let actual_typ = Expr.to_type e in
        check_and_set e actual_typ actual_typ expected_typ
    | None -> (
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
                  ( Type.(mk_set (Expr.to_loc expr) any),
                    Type.(mk_set (Expr.to_loc expr) bot) )
              | _ -> assert false
            in
            check_and_set expr given_type_lb given_type_ub expected_typ
        | (Null | Real _ | Int _ | Bool _ | Empty), _expr_list ->
            Error.type_error (Expr.to_loc expr)
              (Expr.constr_to_string constr ^ " takes no arguments")
        (* Variables, fields, and call expressions *)
        | Var qual_ident, args_list ->
          (let* qual_ident, symbol =
              (* `M.foo` where `M` is an uninstantiated generic functor: try to solve
                 its type argument(s) from the call and rewrite to the instantiation. *)
              resolve_or_implicit qual_ident ~on_miss:(fun () ->
                  try_resolve_implicit_instantiation ~loc:(Expr.to_loc expr) ~qual_ident
                    ~arg_exprs:args_list ~expected_typ)
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
                let* _ =
                  match callable_decl.call_decl_kind with
                  | (Proc | Lemma) when not allow_proc_call ->
                      Error.type_error (Expr.to_loc expr)
                        (Printf.sprintf !"%s %{Ident} can only be called as the right-hand side of an assignment statement, e.g. `x := %{Ident}(...)`. Assign its result to a variable first if you need to use it in an expression"
                          (match callable_decl.call_decl_kind with Proc -> "Procedure" | _ -> "Lemma")
                          callable_decl.call_decl_name callable_decl.call_decl_name)
                  | _ -> Rewriter.return ()
                in
                let* is_ghost_scope = Rewriter.is_ghost_scope in
                let is_ghost_scope =
                  is_ghost_scope ||
                  match callable_decl.call_decl_kind with
                  | Lemma | Pred | Invariant -> true 
                  | Func -> expected_typ |> Type.is_ghost
                  (*List.for_all () ~f:(fun e -> e |> Expr.to_type |> Type.is_ghost)*)
                  | _ -> false
                in
                let* args_list =
                  process_callable_args (Expr.to_loc expr) is_ghost_scope callable_decl args_list
                in
                let* _ =
                  (* If this is an auto lemma, check that it is well-formed *)
                  if callable.call_decl.call_decl_is_auto &&
                     (match callable_decl.call_decl_kind with Lemma -> true | _ -> false)
                  then begin
                    let+ _ =
                      Rewriter.List.iter
                        (callable.call_decl.call_decl_precond @ callable.call_decl.call_decl_postcond)
                        ~f:(fun spec ->
                            let+ is_pure = ProgUtils.is_expr_pure spec.spec_form in
                            if not is_pure then 
                              Error.type_error callable.call_decl.call_decl_loc
                                (Printf.sprintf !"This specification of auto lemma %{Ident} is not pure" callable.call_decl.call_decl_name))
                    in
                    ()
                  end
                  else Rewriter.return ()
                in
                let given_typ = Callable.return_type callable_decl in
                let expr = Expr.App (Var qual_ident, args_list, expr_attr) in
                check_and_set expr given_typ given_typ expected_typ
            | VarDef _ | FieldDef _ ->
                let given_typ =
                  match symbol, args_list with
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
              let ty = match constr with
              | Uminus -> Type.num
              | Not -> Type.bool
              | _ -> assert false
              in ty |> Type.set_ghost_to expected_typ
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
              let ty = match constr with
              | TupleLookUp -> Type.(any)
              | MapLookUp -> Type.(map bot expected_typ)
              | Diff | Union | Inter ->
                  Type.meet expected_typ Type.(set_typed bot)
              | Subseteq -> Type.(set_typed bot)
              | Plus | Minus | Mult | Div | Mod | Gt | Lt | Geq | Leq -> Type.num
              | And | Or -> Type.perm
              | Impl -> Type.bool (* antecedent must be pure *)
              | Elem | Eq -> Type.any
              | _ -> assert false
              in ty |> Type.set_ghost_to expected_typ
            in
            let* expr1 = process_expr expr1 expected_typ1 in
            let typ1 = Expr.to_type expr1 in
            (* infer and propagated expected type of expr2 *)
            let expected_typ2 =
              let ty = match constr with
              | TupleLookUp -> Type.int
              | MapLookUp -> Type.map_dom typ1
              | Diff | Union | Inter | Plus | Minus | Mult | Div | Mod | Subseteq
              | Eq | Gt | Lt | Geq | Leq ->
                  typ1
              | And | Or | Impl -> Type.perm
              | Elem -> Type.(set_typed typ1)
              | _ -> assert false
              in ty |> Type.set_ghost_to expected_typ
            in
            let* expr2 = process_expr expr2 expected_typ2 in
            let typ2 = Expr.to_type expr2 in

            (* backpropagate typ2 to expr1 if needed *)
            let expected_typ1 =
              let ty = match constr with
                | TupleLookUp ->
                  let idx = Expr.to_int expr2 in
                  begin match typ1 with
                    | App (Prod, ts, _) when idx < List.length ts && idx >= 0 -> typ1
                    | App (Prod, ts, _) ->
                      Error.type_error (Expr.to_loc expr2)
                        (Printf.sprintf !"Tuple index %d is out of bounds; %{Type} has %d component(s)" idx typ1 (List.length ts))
                    | App _ ->
                      Error.type_error (Expr.to_loc expr1) (Printf.sprintf !"Expected product type, but found %{Type}" typ1)
                  end
              | MapLookUp -> Type.(map typ2 (Type.map_codom typ1))
              | Diff | Union | Inter | Plus | Minus | Mult | Div | Mod | Subseteq
              | Eq | Gt | Lt | Geq | Leq ->
                  Type.join typ1 typ2
              | And | Or | Impl -> Type.perm
              | Elem -> Type.set_elem typ2
              | _ -> assert false
              in ty |> Type.set_ghost_to expected_typ
            in
            let* expr1 =
              if Type.equal expected_typ1 typ1 then Rewriter.return expr1
              else process_expr expr1 expected_typ1
            in

            let expected_typ =
              let ty =
                if not @@ Type.is_any expected_typ then expected_typ
                else
                  match constr with
                  | TupleLookUp -> Type.tuple_lookup typ1 (Expr.to_int expr2)
                  | MapLookUp -> Type.map_codom typ1
                  | Diff | Union | Inter | Plus | Minus | Mult | Div | Mod -> Type.join typ1 typ2
                  | And | Or | Impl -> expected_typ
                  | Subseteq | Eq | Gt | Lt | Geq | Leq | Elem -> Type.bool
                  | _ -> assert false
              in ty |> Type.set_ghost_to expected_typ
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
                  (Type.(set_typed any), Type.(set_typed bot))
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
              let ty = match constr with
              | Ite -> Type.bool
              | MapUpdate -> Type.(map bot any)
              | _ -> assert false
              in ty |> Type.set_ghost_to expected_typ
            in
            let* expr1 = process_expr expr1 expected_typ1 in
            let typ1 = Expr.to_type expr1 in
            (* infer and propagate expected type of expr2 *)
            let expected_typ2 =
              let ty = match constr with
              | Ite -> expected_typ
              | MapUpdate -> Type.map_dom typ1
              | _ -> assert false
              in ty |> Type.set_ghost_to expected_typ
            in
            let* expr2 = process_expr expr2 expected_typ2 in
            let typ2 = Expr.to_type expr2 in
            (* infer and propagate expected type of expr3 *)
            let expected_typ3 =
              let ty = match constr with
              | Ite -> expected_typ
              | MapUpdate -> Type.map_codom typ1
              | _ -> assert false
              in ty |> Type.set_ghost_to expected_typ
            in
            let* expr3 = process_expr expr3 expected_typ3 in
            let typ3 = Expr.to_type expr3 in
            (* backpropagate typ3 to expr2 if needed *)
            let expected_typ2 =
              let ty = match constr with
              | Ite -> Type.join typ2 typ3
              | MapUpdate -> typ2
              | _ -> assert false
              in ty |> Type.set_ghost_to expected_typ
            in
            let* expr2 =
              if Type.equal expected_typ2 typ2 then Rewriter.return expr2
              else process_expr expr2 expected_typ2
            in
            let typ2 = Expr.to_type expr2 in
            (* backpropagate typ3 and typ2 to expr1 if needed *)
            let expected_typ1 =
              let ty = match constr with
              | Ite -> Type.bool
              | MapUpdate -> Type.map typ2 typ3
              | _ -> assert false
              in ty |> Type.set_ghost_to expected_typ
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
        | ( Own, arg_list ) ->
          let* expr1, expr2, expr3, expr4_opt =
            match arg_list with
            | App (Read, [expr1; (App (Var qual_ident, [], expr_attr') as expr2)], _) as expr12 :: expr3 :: expr4_opt ->
              begin
                let* qual_ident, symbol =
                  Rewriter.resolve_and_find qual_ident
                in
                let+ symbol = Rewriter.Symbol.reify symbol in
                match symbol with
                | FieldDef _ -> expr1, expr2, expr3, expr4_opt
                | _ ->
                  (match expr4_opt with
                  | expr41 :: expr4_opt -> expr12, expr3, expr41, expr4_opt
                  | _ -> Error.type_error (Expr.to_loc expr12) "Expected field location")
              end
            | expr1
              :: (App (Var qual_ident, [], expr_attr') as expr2)
              :: expr3 :: expr4_opt -> Rewriter.return (expr1, expr2, expr3, expr4_opt)
            | _ ->
              Error.type_error (Expr.to_loc expr)
                (Expr.constr_to_string constr
                ^ " takes either three or four arguments, and second argument is a \
                    field name")
            in
            let* expr1 = process_expr expr1 (Type.ref |> Type.set_ghost_to expected_typ)
            and* expr2 = process_expr expr2 (Type.any |> Type.set_ghost_to expected_typ) in

            let* field_type =
              match expr2 with
              | App (Var qual_ident, [], _) ->
                let+ field_def = Rewriter.find_and_reify_field qual_ident in
                field_def.field_type |> Type.field_val |> Type.set_ghost_to expected_typ
              | _ ->
                  Error.type_error (Expr.to_loc expr2)
                    "Expected field identifier"
            in
            let* is_ra_type = ProgUtils.is_ra_type field_type in
            let* expr3 = process_expr expr3 field_type

            (* Implicitely case-split on heap RA vs. other RA *)
            and* expr4_opt =
              match expr4_opt with
              | [] -> 
                if not is_ra_type 
                then Rewriter.return [Expr.mk_real ~loc:(Expr.to_loc expr) 1.0]
                else Rewriter.return []
              | [e] ->
                if is_ra_type
                then Error.type_error (Expr.to_loc e)
                    "'own(...)' for a field whose value is a resource algebra (RA) element does not take an extra fraction argument"
                else
                let+ e = process_expr e (Type.real |> Type.set_ghost_to expected_typ) in
                [e]
              | _ ->
                Error.type_error (Expr.to_loc expr)
                  "Too many arguments supplied to predicate 'own'"
            in
            (* Reconstruct and check expr *)
            let expr =
              Expr.App (Own, expr1 :: expr2 :: expr3 :: expr4_opt, expr_attr)
            in
            check_and_set expr Type.perm Type.perm expected_typ
        | AUPred call_name, token :: args_tuple :: [] ->
            (* Logs.debug (fun m -> m "Typing.ProcessExpr.process_expr: AUPred: args_list=%a" (Util.Print.pr_list_comma Expr.pr) args_list); *)
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
              let* token = process_expr token (Type.atomic_token call_name) in
              let* args_list =
                process_callable_args ~is_called:false loc true callable_decl args_list
              in
              let expr =
                Expr.App (AUPred call_name, [token; Expr.mk_tuple args_list], expr_attr)
              in
              check_and_set expr Type.perm Type.perm expected_typ
        | AUPred _, _ ->
            Error.type_error (Expr.to_loc expr)
              "au<proc>() called with incorrect number of arguments. Expected: first argument: AtomicToken<proc>; second argument: tuple of proc args (or unit)"
        | AUPredCommit call_name, token :: args_tuple :: rets_tuple :: [] ->
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
              let* token = process_expr token (Type.atomic_token call_name) in
              let* args_list =
                process_callable_args ~is_called:false loc true callable_decl args_list
              in
              let* rets_tuple =
                process_expr rets_tuple
                  ((Type.mk_prod loc
                    (List.map callable_decl.call_decl_returns ~f:(fun v ->
                          Logs.debug (fun m -> m !"ret_arg: %{Ident} %b" v.var_name (v.var_type |> Type.is_ghost));
                          v.var_type))) |> Type.set_ghost true)
              in
              let expr =
                Expr.App (AUPredCommit call_name, [token; Expr.mk_tuple args_list; rets_tuple], expr_attr)
              in
              check_and_set expr Type.perm Type.perm expected_typ
        | AUPredCommit _, _ ->
            Error.type_error (Expr.to_loc expr)
              "auCommit<proc>() called with incorrect number of arguments. Expected: first argument: AtomicToken<proc>; second argument: tuple of prog args (or unit); third argument: tuple of proc ret vals (or unit)"
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
            let* destr_qual_ident, destr =
              let* destr_qual_ident, symbol = Rewriter.resolve_and_find destr_qual_ident in
              let+ symbol = Rewriter.Symbol.reify symbol in
              match symbol with
              | DestrDef destr -> destr_qual_ident, destr
              | _tp_env -> Error.type_error loc "Expected data destructor"
            in
            let* expr1 = process_expr expr1 (destr.destr_arg |> Type.set_ghost_to expected_typ) in
            let given_typ = destr.destr_return_type in
            let expr = Expr.App (DataDestr destr_qual_ident, [ expr1 ], expr_attr) in
            check_and_set expr given_typ given_typ expected_typ
        | DataDestr _, _ ->
            Error.type_error (Expr.to_loc expr)
              (Expr.constr_to_string constr ^ " takes exactly one argument")
        (* Read expressions *)
        | Read, [ expr1; App (Var field_ident, [], expr_attr') ] -> (
          let* qual_ident, symbol =
              (* `expr1.M.value` where `M` is an uninstantiated functor: infer from
                 `expr1`'s peeked type, see try_resolve_implicit_instantiation_destr. *)
              resolve_or_implicit field_ident ~on_miss:(fun () ->
                  let* peeked_expr1 =
                    process_expr expr1 (Type.any |> Type.set_ghost_to expected_typ)
                  in
                  try_resolve_implicit_instantiation_destr ~field_ident
                    ~arg_typ:(Expr.to_type peeked_expr1))
            in
            let* symbol = Rewriter.Symbol.reify symbol in
            match symbol with
            | DestrDef _ ->
                process_expr
                  (App (DataDestr qual_ident, [ expr1 ], expr_attr))
                  expected_typ
            | FieldDef _ ->
                Error.type_error (Expr.to_loc expr)
                  (Printf.sprintf !"Cannot read field %{QualIdent} in this context"
                  field_ident)
            | _ ->
                Error.type_error (Expr.to_loc expr)
                  (Printf.sprintf !"Expected destructor identifier, but found %s %{QualIdent}"
                    (Symbol.kind symbol) qual_ident))
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
                  let+ mexpr = process_expr mexpr (elem_typ |> Type.set_ghost_to expected_typ) in
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
              | _ -> List.map ~f:(fun e -> (e, Type.any |> Type.set_ghost_to expected_typ)) elem_expr_list
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
            check_and_set expr given_typ given_typ expected_typ
        (* | _a, exprs -> ProcessExprExt.type_check_expr _a exprs expr_attr *)
        | ExprExt expr_ext, expr_list ->
          let* ext_hooks = Rewriter.current_ext_hooks in
          ext_hooks.type_check_expr expr_ext expr_list expr_attr expected_typ {check_and_set; process_expr; type_mismatch_error; expand_type_expr = ProcessTypeExpr.expand_type_expr}
      )

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
                      process_expr expr (Type.any |> Type.set_ghost true)))
            in

            (* TODO: Add additional checks for triggers *)
            let inner_typ = Expr.to_type inner_expr in
            let expr =
              Expr.Binder (binder, var_decl_list, trgs, inner_expr, expr_attr)
            in
            check_and_set expr Type.bool (Type.perm |> Type.set_ghost_to expected_typ) inner_typ
        | Compr ->
            let var_decl =
              match var_decl_list with
              | [ v ] -> v
              | _ ->
                  Error.type_error (Expr.to_loc expr)
                    "Map/set comprehensions can only quantify over one variable"
            in
            
            let inner_expr_expected_typ =
              let ty = match expected_typ with
              | App (Map, [ _; tp ], _) -> tp
              | _ -> Type.any
              in ty |> Type.set_ghost_to expected_typ
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
            check_and_set expr expr_typ expr_typ expected_typ))

(* end of process_expr *)

  and process_callable_args ?(is_called = true) loc is_ghost_scope callable_decl args_list =
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

    let* () = Rewriter.Logs.debug (fun printers m -> m "Typing.process_callable_args: args_list=%a" (Util.Print.pr_list_comma printers.pr_expr) args_list) in

    (* Check if too few arguments given. *)
    let _ =
      List.drop callable_formals (List.length args_list)
      |> List.find ~f:(fun var_decl -> not @@ var_decl.Type.var_implicit)
      |> Option.iter ~f:(fun decl ->
          Error.type_error loc
          @@ Printf.sprintf !"Explicit argument %s is missing in this call to %{Ident}"
            (Ident.name decl.Type.var_name)
            callable_decl.call_decl_name)
    in

    let provided_formals = List.take callable_formals (List.length args_list) in
    let explicit_formal_types =
      List.map provided_formals ~f:(fun var_decl ->
          var_decl.Type.var_type)
    in
    let* _ = Rewriter.enter_ghost (is_ghost_call || is_ghost_scope) in
    match%bind
      Rewriter.List.map2 args_list explicit_formal_types ~f:(fun expr tp_expr ->
          process_expr expr (tp_expr |> Type.set_ghost (Type.is_ghost tp_expr || is_ghost_call || is_ghost_scope)))
    with
    | Ok args_list ->
      let+ _ = Rewriter.exit_ghost in
      args_list
    | Unequal_lengths ->
        (* Catches if too many args given. *)
        Error.type_error loc
        @@ Printf.sprintf "Too many arguments passed to %s"
            (Ident.to_string callable_decl.call_decl_name)

  and process_callable_returns loc ~is_ghost_scope ~is_call callable_decl returns_list =
    let open Rewriter.Syntax in
    let callable_returns = callable_decl.Callable.call_decl_returns
    in
    let is_ghost_call =
      match callable_decl.call_decl_kind with
      | Pred | Invariant | Lemma -> true
      | _ -> false
    in

    let* () = Rewriter.Logs.debug (fun printers m -> m "Typing.process_callable_returns: callable=%a; returns_list=[%a]" Ident.pr callable_decl.call_decl_name printers.pr_expr_list returns_list) in

    (* Check if too few returns given. *)
    let _ =
      let num_found = List.length returns_list in
      let num_expected = List.length callable_returns in
      if not (num_found = num_expected) then
        Error.type_error loc
        @@ Printf.sprintf !"%s has %d return parameter(s), but found %d return variable(s)"
          (callable_decl.call_decl_name |> Ident.to_string) num_expected num_found
    in

    let provided_returns = List.take callable_returns (List.length returns_list) in
    match%bind
      Rewriter.List.map2 returns_list provided_returns ~f:(fun expr var_decl ->
          let is_ghost =
            (if is_call
            then Type.is_ghost (expr |> Expr.to_type)
            else Type.is_ghost var_decl.Type.var_type)
            || is_ghost_call || is_ghost_scope
          in
          let tp_expr = var_decl.Type.var_type |> Type.set_ghost is_ghost in
          let* () = Rewriter.Logs.debug (fun printers m -> m "%a %a %b" Ident.pr var_decl.var_name printers.pr_type tp_expr is_ghost) in
          let+ expr = process_expr expr tp_expr in
          expr
          )
    with
    | Ok returns_list -> Rewriter.return returns_list
    | Unequal_lengths ->
        (* Catches if too many return values given. *)
        Error.type_error loc
        @@ Printf.sprintf "Too many values returned for %s"
            (Ident.to_string callable_decl.call_decl_name)

  (** Try plain resolution of [qual_ident]; on failure, invoke [on_miss] (one of
      [try_resolve_implicit_instantiation] / [try_resolve_implicit_instantiation_destr])
      and, if it rewrites to a new qual_ident, resolve that instead. [None] if neither
      applies. *)
  and resolve_or_implicit_opt (qual_ident : qual_ident)
      ~(on_miss : unit -> qual_ident option Rewriter.t) :
      (qual_ident * Rewriter.Symbol.t) option Rewriter.t =
    let open Rewriter.Syntax in
    let* resolved = Rewriter.resolve_and_find_opt qual_ident in
    match resolved with
    | Some _ -> Rewriter.return resolved
    | None -> (
        let* rewritten = on_miss () in
        match rewritten with
        | Some rewritten_qual_ident -> Rewriter.resolve_and_find_opt rewritten_qual_ident
        | None -> Rewriter.return None)

  (** [resolve_or_implicit_opt], but raising the ordinary "unknown identifier" error
      instead of returning [None] when [on_miss] doesn't apply either. *)
  and resolve_or_implicit (qual_ident : qual_ident)
      ~(on_miss : unit -> qual_ident option Rewriter.t) :
      (qual_ident * Rewriter.Symbol.t) Rewriter.t =
    let open Rewriter.Syntax in
    let* resolved = resolve_or_implicit_opt qual_ident ~on_miss in
    match resolved with
    | Some resolved -> Rewriter.return resolved
    | None -> Rewriter.resolve_and_find qual_ident

  (** Resolve [qi] as `<functor>.<member>`: split off the prefix, resolve it, and check
      it names a functor eligible for implicit instantiation (see
      [ProgUtils.is_generic_functor]). [None] if [qi] is unqualified, its prefix
      doesn't resolve, or isn't such a functor. Shared by
      [try_resolve_implicit_instantiation] and
      [try_resolve_implicit_instantiation_destr]. *)
  and resolve_generic_functor_prefix (qi : qual_ident) :
      (qual_ident * Module.t * ident) option Rewriter.t =
    let open Rewriter.Syntax in
    if List.is_empty (QualIdent.path qi) then Rewriter.return None
    else
      let functor_qi_written = QualIdent.pop qi in
      let member_ident = QualIdent.unqualify qi in
      let+ functor_resolved = ProgUtils.resolve_generic_functor functor_qi_written in
      Option.map functor_resolved ~f:(fun (functor_qual_ident, m) ->
          (functor_qual_ident, m, member_ident))

  (** Check whether [qi] is (an alias for) an instantiation of the functor resolved as
      [functor_qual_ident]: an instantiation's alias resolves back to
      [functor_qual_ident] itself, via [Rewriter.Symbol.orig_qid]. *)
  and resolves_to_instantiation_of ~(functor_qual_ident : qual_ident) (qi : qual_ident) :
      bool Rewriter.t =
    let open Rewriter.Syntax in
    let+ resolved = Rewriter.resolve_and_find_opt qi in
    match resolved with
    | Some (_, symbol) -> QualIdent.equal (Rewriter.Symbol.orig_qid symbol) functor_qual_ident
    | None -> false

  (** Check whether [typ] (normalized via [ProcessTypeExpr.process_type_expr], in case
      it's a raw, self-referentially-read-back type) names an existing instantiation
      of functor [m]; return that instantiation's qualified name on success. *)
  and resolve_existing_instantiation ~(functor_qual_ident : qual_ident) (m : Module.t)
      (typ : type_expr) : qual_ident option Rewriter.t =
    let open Rewriter.Syntax in
    match m.mod_decl.mod_decl_rep with
    | None -> Rewriter.return None
    | Some rep_ident -> (
        let* typ = ProcessTypeExpr.process_type_expr typ in
        match typ with
        | App (Var qi, [], _)
          when Ident.equal (QualIdent.unqualify qi) rep_ident
               && not (List.is_empty (QualIdent.path qi)) -> (
            let inst_qi = QualIdent.pop qi in
            let* is_inst = resolves_to_instantiation_of ~functor_qual_ident inst_qi in
            Rewriter.return (if is_inst then Some inst_qi else None))
        | _ -> Rewriter.return None)

  (** Unify [pairs] against each other, threading (and extending) the partial solution
      [u] from [m]'s formals to the concrete types they've been solved to so far. Each
      pair `(t1, t2)` is `t1`, a type written inside [m]'s own un-instantiated body
      (e.g. a parameter's declared type), against `t2`, the corresponding concrete type
      from the call site (e.g. an argument's inferred type). Deliberately a structural
      approximation, not a full algorithm (no union-find, no occurs check) -- see
      [unify_one] below for the three cases it distinguishes. *)
  and unify_type_list ~(loc : location) ~(functor_qual_ident : qual_ident) (m : Module.t)
      (u : (ident * type_expr) list) (pairs : (type_expr * type_expr) list) :
      (ident * type_expr) list Rewriter.t =
    let open Rewriter.Syntax in
    (* [formal_reps]: each of [m]'s formals' rep-qualident within [m] (the "unification
       variables" `t1` can bind); [m_rep_qi]: [m]'s own rep-qualident. *)
    let* formal_reps =
      Rewriter.List.map m.mod_decl.mod_decl_formals ~f:(fun formal ->
          let+ rep = ProgUtils.resolve_rep_ident formal.mod_inst_type in
          Base.Option.map rep ~f:(fun (_, rep_ident) ->
              ( QualIdent.append
                  (QualIdent.append functor_qual_ident formal.mod_inst_name)
                  rep_ident,
                formal.mod_inst_name,
                rep_ident )))
    in
    let formal_reps = List.filter_opt formal_reps in
    let m_rep_qi =
      Base.Option.map m.mod_decl.mod_decl_rep ~f:(QualIdent.append functor_qual_ident)
    in
    (* Canonicalize via [expand_type_expr] before storing/comparing: two bindings for
       the same formal can be the same type reached through different alias chains
       (e.g. `Int` vs. `GenInst$$M$$Int.T.T`), which would otherwise look like a
       conflict. *)
    let combine u formal_ident t2 =
      let* t2 = ProcessTypeExpr.expand_type_expr (t2 |> Type.set_ghost false) in
      match List.Assoc.find u formal_ident ~equal:Ident.equal with
      | Some prior when not (Type.equal prior t2) ->
          Error.type_error loc
            (Printf.sprintf
               !"Cannot infer a single type for parameter %{Ident} of %{QualIdent}: \
                 found both %{Type} and %{Type}"
               formal_ident functor_qual_ident prior t2)
      | Some _ -> Rewriter.return u
      | None -> Rewriter.return (List.Assoc.add u formal_ident t2 ~equal:Ident.equal)
    in
    let same_head c1 c2 =
      Type.equal
        (Type.App (c1, [], Type.dummy_attr) |> Type.set_ghost false)
        (Type.App (c2, [], Type.dummy_attr) |> Type.set_ghost false)
    in
    let rec go u = function
      | [] -> Rewriter.return u
      | (t1, t2) :: pairs ->
          let* u = unify_one u t1 t2 in
          go u pairs
    and unify_one u t1 t2 =
      (* Normalize only [t2]: [t1] names [m]'s own formals/rep, which are by design
         unreachable via ordinary resolution from outside [m] -- it's only ever
         pattern-matched against [formal_reps]/[m_rep_qi] below, never resolved. *)
      let* t2 = ProcessTypeExpr.process_type_expr t2 in
      if Type.is_any (t1 |> Type.set_ghost false) || Type.is_any (t2 |> Type.set_ghost false)
      then Rewriter.return u
      else
        (* Three cases: `t1` is a formal's rep (bind/check it against `t2`); `t1` is
           [m]'s own rep and `t2` is an existing instantiation (read off all formals at
           once); or both sides recurse structurally on matching head/arity. *)
        match
          List.find formal_reps ~f:(fun (rep_qi, _, _) ->
              match t1 with
              | App (Var qi, [], _) -> QualIdent.equal rep_qi qi
              | _ -> false)
        with
        | Some (_, formal_ident, _) -> combine u formal_ident t2
        | None -> (
            match t1 with
            | App (Var qi, [], _)
              when (match m_rep_qi with Some r -> QualIdent.equal qi r | None -> false)
              -> (
                match t2 with
                | App (Var qi2, [], _) -> (
                    let inst_qi = QualIdent.pop qi2 in
                    let* is_inst = resolves_to_instantiation_of ~functor_qual_ident inst_qi in
                    if not is_inst then Rewriter.return u
                    else
                      Rewriter.List.fold_left formal_reps ~init:u
                        ~f:(fun u (_, formal_ident, rep_ident) ->
                          combine u formal_ident
                            (Type.mk_var
                               (QualIdent.append
                                  (QualIdent.append inst_qi formal_ident)
                                  rep_ident))))
                | _ -> Rewriter.return u)
            | App (c1, args1, _) -> (
                match t2 with
                | App (c2, args2, _)
                  when Int.equal (List.length args1) (List.length args2) && same_head c1 c2
                  -> go u (List.zip_exn args1 args2)
                | _ ->
                    Error.type_error loc
                      (Printf.sprintf !"Cannot unify type %{Type} with type %{Type}" t1 t2)))
    in
    go u pairs

  (** Try to resolve [qual_ident] (e.g. `M.foo`, already failed plain resolution) as a
      call into a member of an uninstantiated generic functor, implicitly instantiating
      it. [None] if [qual_ident] isn't `<functor>.<member>`-shaped, or the functor/member
      doesn't exist; once both exist, either succeeds or raises (the real problem is
      inference, not a typo). Solves [m]'s formals via [unify_type_list], unifying each
      argument's peeked type against its formal's declared type, plus the member's own
      return type against [expected_typ]. *)
  and try_resolve_implicit_instantiation ~(loc : location) ~(qual_ident : qual_ident)
      ~(arg_exprs : expr list) ~(expected_typ : type_expr) : qual_ident option Rewriter.t
      =
    let open Rewriter.Syntax in
    let* prefix = resolve_generic_functor_prefix qual_ident in
    match prefix with
    | None -> Rewriter.return None
    | Some (functor_qual_ident, m, member_ident) -> (
        (* The member can be an ordinary callable or a data constructor -- both are
           addressable as `<module>.<member>(...)` and solved identically below. *)
        let member_info =
          List.find_map m.mod_def ~f:(function
            | SymbolDef (CallDef call_def)
              when Ident.equal (Callable.to_decl call_def).call_decl_name member_ident
              ->
                let call_decl = Callable.to_decl call_def in
                let return_type =
                  match call_decl.call_decl_returns with
                  | [ r ] -> Some r.Type.var_type
                  | _ -> None
                in
                Some (call_decl.call_decl_formals, return_type)
            | SymbolDef (ConstrDef constr_def)
              when Ident.equal constr_def.constr_name member_ident ->
                Some (constr_def.constr_args, Some constr_def.constr_return_type)
            | _ -> None)
        in
        match member_info with
        | None -> Rewriter.return None
        | Some (member_formals, return_type_opt) ->
            if List.length member_formals <> List.length arg_exprs then
              arg_mismatch_error "Callable" loc (Type.Var qual_ident)
                (List.length member_formals)
            else
              (* Peek each argument's type; the processed expr itself is discarded and
                 reprocessed once the instantiation is resolved. *)
              let* arg_pairs =
                Rewriter.List.map2_exn member_formals arg_exprs
                  ~f:(fun formal_var_decl arg_expr ->
                    let+ arg_expr =
                      process_expr arg_expr (Type.any |> Type.set_ghost_to expected_typ)
                    in
                    let arg_typ = Expr.to_type arg_expr in
                    (* An underdetermined literal (e.g. `{||}`) peeked with no expected
                       type gives `Bot` for its missing type information -- that's not a
                       real type argument to solve the instantiation with, so reject it
                       here instead of letting it flow into a bogus instantiation. *)
                    if Type.contains_bot arg_typ then
                      Error.type_error (Expr.to_loc arg_expr)
                        (Printf.sprintf
                           !"Cannot infer a type argument for %{QualIdent} from this \
                             argument: the type of `%{Expr}` cannot be uniquely \
                             determined here. Give it an explicit type annotation, or \
                             write an explicit instantiation, e.g. `module M_X = \
                             %{QualIdent}[...]`"
                           functor_qual_ident arg_expr functor_qual_ident)
                    else (formal_var_decl.Type.var_type, arg_typ))
              in
              let pairs =
                match return_type_opt with
                | Some return_type -> (return_type, expected_typ) :: arg_pairs
                | None -> arg_pairs
              in
              let* bindings = unify_type_list ~loc ~functor_qual_ident m [] pairs in
              (match
                 List.find m.mod_decl.mod_decl_formals ~f:(fun formal ->
                     not
                       (List.Assoc.mem bindings formal.mod_inst_name ~equal:Ident.equal))
               with
              | Some formal ->
                  Error.type_error loc
                    (Printf.sprintf
                       !"Cannot infer a type argument for parameter %{Ident} of \
                         %{QualIdent}; write an explicit instantiation, e.g. `module \
                         M_X = %{QualIdent}[...]`"
                       formal.mod_inst_name functor_qual_ident functor_qual_ident)
              | None ->
                  let arg_types =
                    List.map m.mod_decl.mod_decl_formals ~f:(fun formal ->
                        List.Assoc.find_exn bindings formal.mod_inst_name
                          ~equal:Ident.equal)
                  in
                  let+ inst_qual_ident =
                    ProgUtils.instantiate_type_functor ~loc ~f:!(Rewriter.process_symbol_ref)
                      ~functor_qual_ident ~functor_mod_decl:m.mod_decl arg_types
                  in
                  Some (QualIdent.append inst_qual_ident member_ident)))

  (** The `Read`-expression (`expr1.M.value`) counterpart of
      [try_resolve_implicit_instantiation]. A destructor has no arguments to infer a
      type from, only [arg_typ] ([expr1]'s peeked type) -- so this only succeeds when
      [arg_typ] already names an existing instantiation of `M`, rewriting to that
      instantiation's destructor. *)
  and try_resolve_implicit_instantiation_destr ~(field_ident : qual_ident)
      ~(arg_typ : type_expr) : qual_ident option Rewriter.t =
    let open Rewriter.Syntax in
    let* prefix = resolve_generic_functor_prefix field_ident in
    match prefix with
    | None -> Rewriter.return None
    | Some (functor_qual_ident, m, member_ident) ->
        let has_member =
          List.exists m.mod_def ~f:(function
            | SymbolDef (DestrDef destr_def) -> Ident.equal destr_def.destr_name member_ident
            | _ -> false)
        in
        if not has_member then Rewriter.return None
        else
          let+ inst_qi_opt = resolve_existing_instantiation ~functor_qual_ident m arg_typ in
          Option.map inst_qi_opt ~f:(fun inst_qi -> QualIdent.append inst_qi member_ident)
end


module ProcessCallable = struct
  open ProgUtils
  let disambiguate_ident (qual_ident : qual_ident)
      (disam_tbl : DisambiguationTbl.t) : qual_ident Rewriter.t =
    let open Rewriter.Syntax in
    if QualIdent.is_local qual_ident then
      let ident = qual_ident |> QualIdent.unqualify in
      let* base =
        if Predefs.is_qual_ident_au_cmnd qual_ident then
          Rewriter.return ident
        else
          match DisambiguationTbl.find disam_tbl ident with
          | Some iden -> Rewriter.return iden
          | None ->
              let* is_local =
                Rewriter.is_local qual_ident
              in
              if is_local then
                (* if variable is local and it doesn't exist in DisambiguationTbl, then it is not defined in scope *)
                error (QualIdent.to_loc qual_ident)
                @@ Printf.sprintf "Identifier %s unbound in scope"
                     (Ident.to_string qual_ident.qual_base)
              else Rewriter.return qual_ident.qual_base
      in
      Rewriter.return (QualIdent.make [] base |> QualIdent.set_loc (QualIdent.to_loc qual_ident))
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
        let* () = Rewriter.Logs.debug (fun printers m -> m
          "typing.ProcessCallable.disambiguate_expr: expr = %a"
            printers.pr_expr expr
        ) in
        let* disambiguated_expr = disambiguate_expr expr disam_tbl in
        let* trgs =
          Rewriter.List.map trgs ~f:(fun trg ->
              Rewriter.List.map trg ~f:(fun expr ->
                  disambiguate_expr expr disam_tbl))
        in

        Rewriter.return
          Expr.(
            Binder (binder, var_decl_list, trgs, disambiguated_expr, expr_attr))

  let disambiguate_process_expr ?(allow_proc_call = false) (expr : expr) (expected_typ : type_expr)
      (disam_tbl : DisambiguationTbl.t) : expr Rewriter.t =
    let open Rewriter.Syntax in
    let* expr = disambiguate_expr expr disam_tbl in
    let* printers = Rewriter.current_printers in

    let+ processed_expr =
      ProcessExpr.process_expr ~allow_proc_call expr expected_typ
    in

    Logs.debug (fun m -> m
      "Typing.ProcessCallable.disambiguate_process_expr: processed_expr = %a"
      printers.pr_expr processed_expr
    );
    
    processed_expr

  let disambiguate_process_field_read ref field disam_tbl =
    let open Rewriter.Syntax in
    let* field, symbol =
      Rewriter.resolve_and_find field
    in
    let* symbol = Rewriter.Symbol.reify symbol in
    match symbol with
    | FieldDef { field_type = App (Fld, [ field_type ], _); _ } ->
      let+ ref = disambiguate_process_expr ref Type.ref disam_tbl in
      ref, field, field_type, symbol
    | DestrDef { destr_arg; destr_return_type; _ } ->
      let+ arg = disambiguate_process_expr ref destr_arg disam_tbl in
      arg, field, destr_return_type, symbol      
    | _ -> Error.type_error (QualIdent.to_loc field) (Printf.sprintf !"Expected field identifier but found %s %{QualIdent}" (Symbol.kind symbol) field)

  
  let process_stmt_spec (disam_tbl : DisambiguationTbl.t) (spec : Stmt.spec) :
      Stmt.spec Rewriter.t =
    let open Rewriter.Syntax in
    let* _ = Rewriter.enter_ghost true in
    let* spec_form =
      disambiguate_process_expr spec.spec_form Type.perm disam_tbl
    in
    let+ _ = Rewriter.exit_ghost in
    { spec with spec_form }

  (* let rec purify_expr (expr: expr) (tbl: SymbolTbl.t) : Stmt.var_def list * expr =
     (* Takes an expr, and returns a pure expression along with a set of temp variables that need to be defined  *)
     () *)

  let process_au_action_stmt (call_decl: Callable.call_decl) (assign_lhs: qual_ident list) (var_decls_lhs: var_decl list) qual_ident args (loc : location)
      (disam_tbl : DisambiguationTbl.t) :
      (Stmt.basic_stmt_desc * DisambiguationTbl.t) Rewriter.t =
    let open Rewriter.Syntax in
    let _ = List.iter2_exn assign_lhs var_decls_lhs ~f:(fun qual_ident var_decl ->
        if var_decl.var_type |> Type.is_ghost then () else
          Error.type_error (qual_ident |> QualIdent.to_loc) "Ghost command cannot assign to non-ghost variable"
      )
    in
    match args with
    | _ when QualIdent.(qual_ident = QualIdent.from_ident Predefs.fpu_ident) ->
      (* fpu *)
      let field_opt = function
          | Expr.App (Var qual_ident, [], _) ->
            let* field_qual_ident, symbol =
              Rewriter.resolve_and_find qual_ident
            in
            let+ symbol = Rewriter.Symbol.reify symbol in
            begin match symbol with
              | FieldDef field_decl when not field_decl.field_is_ghost ->
                Error.type_error (QualIdent.to_loc qual_ident)
                  "Frame-preserving updates ('fpu') can only be applied to ghost fields whose value is a resource algebra (RA) element"
              | FieldDef { field_type = App (Fld, [ given_type ], _); _ }  ->
                Some (field_qual_ident, given_type)
              | _ -> None
            end
          | _ -> Rewriter.return None
        in
        let* ref_expr, field, fpu_exprs =
          let* opt_list = 
            match args with
            | Expr.App (Read, [ref_expr; field_expr], _) :: expr2 :: expr3_opt ->
              let* field = field_opt field_expr in
              field |> Rewriter.Option.map ~f:(fun field ->
                  Rewriter.return (ref_expr, field, expr2 :: expr3_opt))
            | _ -> Rewriter.return None
          in
          opt_list
          |> Rewriter.Option.lazy_value ~default:(fun () ->
              match args with
              | expr1 :: expr2 :: expr3_opt ->
                let* field = field_opt expr2 in
                let* field = Rewriter.Option.map field ~f:(fun field_qual_ident ->
                    Rewriter.return (expr1, field_qual_ident, expr3_opt))
                in
                Rewriter.Option.lazy_value field
                  ~default:(fun () -> Error.type_error (Expr.to_loc expr1) "Expected field location")
              | _ -> Error.type_error loc "Could not find field location in fpu"
            )
        in
        let* ref_expr =
          disambiguate_process_expr ref_expr (Type.ref |> Type.set_ghost true) disam_tbl
        in
        let field_qual_ident, given_type = field in
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
        
        ( Stmt.Fpu
               {
                 fpu_ref = ref_expr;
                 fpu_field = field_qual_ident;
                 fpu_old_val = old_val_expr;
                 fpu_new_val = new_val_expr;
               },
          disam_tbl )
    | _ when QualIdent.(qual_ident = QualIdent.from_ident Predefs.bindAU_ident) ->
      (* bindAU *)
        begin match args, assign_lhs with
        | [], [ token_qual_ident ] ->
          let* proc_qual_ident = Rewriter.current_scope_id in
          let* token = Rewriter.find_and_reify_var token_qual_ident in
          let token_expr = Expr.mk_var ~typ:token.var_decl.var_type token_qual_ident in
          let+ _ = ProcessExpr.process_expr token_expr (Type.atomic_token proc_qual_ident) in
          (* TODO: check type Type.atomic_token *)
          ( Stmt.AUAction { auaction_kind = BindAU token_qual_ident },
            disam_tbl )
        | _ -> Error.type_error loc "bindAU takes no arguments"
        end
    | token :: args ->
      let* token =
        disambiguate_process_expr token (Type.any |> Type.set_ghost true) disam_tbl
      in
      let* proc_qual_ident =
        match Expr.to_type token with
        | App (AtomicToken proc_qual_ident, [], _) -> 
          let+ proc_qual_ident = Rewriter.resolve proc_qual_ident in
          proc_qual_ident
        | typ ->
          type_mismatch_error (Expr.to_loc token) (Type.atomic_token (Ident.make Loc.dummy "?" 0 |> QualIdent.from_ident)) typ
      in

      let* proc_call_decl = 
        let+ proc_callable = Rewriter.find_and_reify_callable proc_qual_ident in
        proc_callable.call_decl
      in

      let* proc_args = 
        let proc_concrete_in_args = List.filter proc_call_decl.call_decl_formals ~f:(fun var_decl -> not var_decl.var_implicit) in
        
        let in_args_supplied = begin match args with
          | in_args :: [] when QualIdent.(qual_ident = from_ident Predefs.openAU_ident || qual_ident = from_ident Predefs.abortAU_ident) ->
            true 
          | in_args :: ret :: [] when QualIdent.(qual_ident = from_ident Predefs.commitAU_ident) ->
            true
          | [] when QualIdent.(qual_ident = from_ident Predefs.openAU_ident || qual_ident = from_ident Predefs.abortAU_ident) ->
            false
          | ret :: [] when QualIdent.(qual_ident = from_ident Predefs.commitAU_ident) ->
            false
          | _ ->
            Error.type_error loc "Incorrect number of arguments supplied to AU operator."
          end 
        in

        match in_args_supplied with
        | true ->
          let in_args_tuple = List.hd_exn args in

          let tuple_tp = Type.mk_prod loc (List.map proc_concrete_in_args ~f:(fun arg_var_decl -> arg_var_decl.var_type)) |> Type.set_ghost true in

          let* in_args_tuple = disambiguate_process_expr in_args_tuple tuple_tp disam_tbl in
          let in_args = Expr.unfold_tuple in_args_tuple in
          Rewriter.return in_args

        | false -> 
          let* curr_callable_qi = Rewriter.current_scope_id in
          if QualIdent.(proc_qual_ident = curr_callable_qi) then
            let curr_callable_concrete_args = List.filter call_decl.call_decl_formals ~f:(fun var_decl -> not var_decl.var_implicit) in

            let+ curr_callable_concrete_arg_exprs = Rewriter.List.map curr_callable_concrete_args ~f:(fun arg ->
              let+ var_def = Rewriter.find_and_reify_var (QualIdent.from_ident arg.var_name) in
              Expr.from_var_decl var_def.var_decl
            ) in
            curr_callable_concrete_arg_exprs
          else
            Error.type_error loc "Incorrect number of arguments supplied to AU operator; expected in-args (as a single tuple) since another procedure's atomicToken is being manipulated."
      in
      (* openAU *) 
      if
        QualIdent.(qual_ident = QualIdent.from_ident Predefs.openAU_ident)
      then
        let implicit_vars =
          Base.List.map2_exn assign_lhs var_decls_lhs ~f:(fun qual_ident var_decl ->
              Expr.mk_var ~typ:var_decl.var_type qual_ident)
        in
        let implicit_expected_types =
          Base.List.filter_map proc_call_decl.call_decl_formals ~f:(fun var_decl ->
              if var_decl.var_implicit then Some var_decl.var_type
              else None)
        in
        if List.(not (length implicit_expected_types = length implicit_vars)) then
          Error.type_error loc (Printf.sprintf !"Incorrect number of implicit arguments supplied on LHS for %{QualIdent}" proc_qual_ident)
        else
        let args = Expr.mk_tuple ~loc implicit_vars in
        let+ _ = ProcessExpr.process_expr args ((Type.mk_prod loc implicit_expected_types) |> Type.set_ghost true) in
        ( Stmt.AUAction
            {
              auaction_kind =
                OpenAU { token; proc_qi = proc_qual_ident; proc_args; lhs = implicit_vars;  };
            },
          disam_tbl )
      else if
        QualIdent.(
          qual_ident = QualIdent.from_ident Predefs.commitAU_ident)
      then
        (* commitAU *)
        let returns_tuple = List.last_exn args in
        let* returns =
          Rewriter.List.map (Expr.unfold_tuple returns_tuple) ~f:(fun e -> disambiguate_expr e disam_tbl)
        in
        let* proc =
          Rewriter.find_and_reify_callable proc_qual_ident |+> fun c -> c.call_decl
        in
        let* () = Rewriter.Logs.debug (fun printers m -> m "Typing.process_au_action_stmt: commitAU: returns = [ %a ]" printers.pr_expr_list returns) in
        let+ returns = ProcessExpr.process_callable_returns loc ~is_ghost_scope:true ~is_call:false proc returns in
        ( Stmt.AUAction
            {
              auaction_kind = CommitAU { token; proc_args; proc_rets = returns };
            },
          disam_tbl )
      else if
        QualIdent.(
          qual_ident = QualIdent.from_ident Predefs.abortAU_ident)
      then
        (* abortAU *)
        (* match args with
        | _ :: _ ->
          Error.type_error loc (Printf.sprintf !"%{QualIdent} expects exactly one argument" qual_ident)
        | [] ->  *)
          Rewriter.return
            ( Stmt.AUAction { auaction_kind = AbortAU { token; proc_args } },
              disam_tbl )
      else Error.type_error loc
        (Printf.sprintf !"'%{QualIdent}' is not a recognized atomic-update (AU) action (expected one of bindAU, openAU, commitAU, abortAU, ...)" qual_ident)
    | _ ->
      Error.type_error loc
        (Printf.sprintf !"%{QualIdent} expects at least one argument" qual_ident)
        
  let rec process_basic_stmt call_decl
      (basic_stmt : Stmt.basic_stmt_desc) (stmt_loc: Loc.t) (disam_tbl : DisambiguationTbl.t) :
      (Stmt.basic_stmt_desc * DisambiguationTbl.t) Rewriter.t =
    let open Rewriter.Syntax in
    let* is_ghost_scope = Rewriter.is_ghost_scope in
    let get_assign_lhs ~is_init ?(is_ghost_cmd=false) orig_qual_ident =
      let* qual_ident = disambiguate_ident orig_qual_ident disam_tbl in
      let* qual_ident, symbol =
        Rewriter.resolve_and_find qual_ident
      in
      let+ symbol = Rewriter.Symbol.reify symbol in
      match symbol with
      | VarDef { var_decl; _ } when (is_ghost_scope || is_ghost_cmd) && not var_decl.var_ghost ->
        Error.type_error (QualIdent.to_loc qual_ident)
          (Printf.sprintf !"Cannot assign to non-ghost var %{QualIdent} in ghost context" orig_qual_ident)
      | VarDef { var_decl; _ } when not var_decl.var_const || is_init ->
        qual_ident, var_decl
      | _ ->
        Error.type_error (QualIdent.to_loc qual_ident)
          (Printf.sprintf !"Cannot assign to %s %{QualIdent}" (Symbol.kind symbol) orig_qual_ident)
    in
    match basic_stmt with
    | VarDef var_def ->
      let* var_decl =
        ProcessTypeExpr.process_var_decl var_def.var_decl
      in
      let* curr_callable = Rewriter.current_scope_id in
      let var_ghost = var_decl.var_ghost || is_ghost_scope in 
      let* var_type =
        match var_def.var_init with
        | None -> Rewriter.return var_decl.var_type
        | Some (App (Var qual_ident, _, _)) when Predefs.is_qual_ident_au_cmnd qual_ident ->
          Rewriter.return @@
          if Ident.(Predefs.bindAU_ident = QualIdent.unqualify qual_ident) then
            Type.mk_atomic_token (QualIdent.to_loc qual_ident) curr_callable
          else Type.meet var_decl.var_type Type.any
        | Some (App (Read, [ expr1; field_expr ], _)) ->
          let field_qual_ident = Expr.to_qual_ident field_expr in
          let* _, symbol =
            (* `expr1.M.value` where `M` is an uninstantiated functor, see
               ProcessExpr.try_resolve_implicit_instantiation_destr. *)
            ProcessExpr.resolve_or_implicit field_qual_ident ~on_miss:(fun () ->
                let* peeked_expr1 =
                  disambiguate_process_expr expr1 (Type.any |> Type.set_ghost var_ghost)
                    disam_tbl
                in
                ProcessExpr.try_resolve_implicit_instantiation_destr
                  ~field_ident:field_qual_ident ~arg_typ:(Expr.to_type peeked_expr1))
          in
          let+ symbol = Rewriter.Symbol.reify symbol in
          begin match symbol with
            | FieldDef { field_type = App (Fld, [typ], _); _ } -> typ
            | DestrDef destr_def -> destr_def.destr_return_type
            | _ -> Type.meet var_decl.var_type Type.any
          end
        | Some expr ->
          let+ expr =
            disambiguate_process_expr expr (var_decl.var_type |> Type.set_ghost var_ghost) disam_tbl ~allow_proc_call:true
          in
          Expr.to_type expr
      in
      let var_decl =
        if not (Type.equal var_type Type.any) then
          { var_decl with
            var_type = var_type |> Type.set_ghost var_ghost;
            var_ghost
          }
        else
          Error.error var_decl.var_loc
          @@ Printf.sprintf "Type annotation missing for variable %s"
            (Ident.to_string var_decl.var_name)
      in
      let var_decl, disam_tbl' =
        DisambiguationTbl.add_var_decl var_decl disam_tbl
      in
      let* _ =
        Rewriter.introduce_symbol
          (VarDef { var_decl; var_init = None; var_is_free = false })
      in
      let var = QualIdent.from_ident var_decl.var_name in
      Rewriter.return @@ (Stmt.Havoc { havoc_var = var; havoc_is_init = true }, disam_tbl')
    | Spec (sk, spec) ->
      let+ spec = process_stmt_spec disam_tbl spec in
      (Stmt.Spec (sk, spec), disam_tbl)
    | Assign assign_desc -> begin
        let* assign_lhs, var_decls_lhs =
          Rewriter.List.fold_right assign_desc.assign_lhs ~init:([], [])
            ~f:(fun orig_qual_ident (assign_lhs, var_decls_lhs) ->
                let+ qual_ident, var_decl = get_assign_lhs orig_qual_ident ~is_init:assign_desc.assign_is_init in
                qual_ident :: assign_lhs, var_decl :: var_decls_lhs
            )
        in

        match assign_desc.assign_rhs with
        (* Field read *)
        | App (Read, [ ref_expr; read_expr ], _) ->
          let read_expr_qi = Expr.to_qual_ident read_expr in

          let* read_expr_qi, read_symbol =
            (* `ref_expr.M.value` where `M` is an uninstantiated functor, see
               ProcessExpr.try_resolve_implicit_instantiation_destr. *)
            ProcessExpr.resolve_or_implicit read_expr_qi ~on_miss:(fun () ->
                let* peeked_ref_expr =
                  disambiguate_process_expr ref_expr (Type.any |> Type.set_ghost is_ghost_scope)
                    disam_tbl
                in
                ProcessExpr.try_resolve_implicit_instantiation_destr
                  ~field_ident:read_expr_qi ~arg_typ:(Expr.to_type peeked_ref_expr))
          in
          let* read_symbol = Rewriter.Symbol.reify read_symbol in

          begin match read_symbol with
          | FieldDef f ->

            let* () = Rewriter.Logs.debug (fun printers m ->
                m "process_stmt: read_assign_rhs: %a" printers.pr_expr
                  assign_desc.assign_rhs) in
            let field_qual_ident = read_expr_qi in
            let field_read_lhs =
              match assign_desc.assign_lhs with
              | [ lhs ] -> lhs
              | _ ->
                Error.type_error stmt_loc
                  "Expected exactly one variable on left-hand side of field read"
            in
            
            let field_read_desc =
              Stmt.
                {
                  field_read_lhs;
                  field_read_field = field_qual_ident;
                  field_read_ref = ref_expr;
                  field_read_is_init = assign_desc.assign_is_init;
                }
            in
            Logs.debug (fun m -> m "process_stmt: starting a fieldRead processing");
            process_basic_stmt call_decl (Stmt.FieldRead field_read_desc) stmt_loc disam_tbl
          
          | DestrDef destr_def ->
            let assign_rhs = Expr.mk_app ~loc:stmt_loc ~typ:destr_def.destr_return_type (Expr.DataDestr read_expr_qi) [ref_expr] in
            process_basic_stmt call_decl (Stmt.Assign { assign_desc with assign_rhs}) stmt_loc disam_tbl

          | _ ->
            Error.type_error stmt_loc
              (Printf.sprintf "Expected a data destructor on the right-hand side of this field read, but found %s" (Symbol.kind read_symbol))
          end
        (* AU action *)
        | App (Var qual_ident, args, _) when Predefs.is_qual_ident_au_cmnd qual_ident ->
          process_au_action_stmt call_decl assign_lhs var_decls_lhs qual_ident args stmt_loc disam_tbl
        | _ -> 
          let* () = Rewriter.Logs.debug (fun printers m ->
              m "process_stmt: assign_desc: %a" printers.pr_stmt_basic
                (Assign assign_desc)) in
                  
          let* assign_rhs_callable_opt =
            match assign_desc.assign_rhs with
            | App (Var qual_ident, args, _) -> (
              let* qual_ident =
                disambiguate_ident qual_ident disam_tbl
              in
              (* Peek at whether the RHS is a procedure/lemma call, without raising if
                 it doesn't resolve as-is -- `M.foo` may still resolve via implicit
                 functor instantiation. Falls through to the ordinary expression path
                 (and its error) otherwise. *)
              let* resolved =
                ProcessExpr.resolve_or_implicit_opt qual_ident ~on_miss:(fun () ->
                    (* `args` needs disambiguating here since try_resolve_implicit_instantiation's
                       argument peek doesn't disambiguate local identifiers itself. *)
                    let* args =
                      Rewriter.List.map args ~f:(fun e -> disambiguate_expr e disam_tbl)
                    in
                    ProcessExpr.try_resolve_implicit_instantiation ~loc:stmt_loc
                      ~qual_ident ~arg_exprs:args
                      ~expected_typ:(Type.any |> Type.set_ghost is_ghost_scope))
              in
              match resolved with
              | None -> Rewriter.return None
              | Some (qual_ident, symbol) ->
                  let+ symbol = Rewriter.Symbol.reify symbol in
                  (match symbol with
                  | CallDef call_def -> Some (symbol, qual_ident, args)
                  | _ -> None))
            | _ -> Rewriter.return None
          in
                  

          match assign_rhs_callable_opt with
          | Some (symbol, proc_qual_ident, args) ->
            begin
              Logs.debug (fun m ->
                  m "process_stmt: assign_rhs_qual_ident: %a; %b"
                    QualIdent.pr proc_qual_ident
                    QualIdent.(
                      proc_qual_ident
                      = QualIdent.from_ident Predefs.bindAU_ident));
              
              let (call_desc : Stmt.call_desc) =
                {
                  call_lhs = assign_desc.assign_lhs;
                  (*List.map var_decls_lhs ~f:(fun var -> var.var_name |> QualIdent.from_ident);*)
                  call_name = proc_qual_ident;
                  call_args = args;
                  call_is_spawn = false;
                  call_is_init = assign_desc.assign_is_init
                }
              in                      
              process_basic_stmt call_decl (Stmt.Call call_desc) stmt_loc disam_tbl
              (*(Stmt.Call call_desc, disam_tbl)*)
            end
          | None ->
            let expected_type =
              Type.mk_prod
                (Expr.to_loc assign_desc.assign_rhs)
                (List.map var_decls_lhs ~f:(fun var -> var.var_type))
              |> fun ty -> if is_ghost_scope then ty |> Type.set_ghost true else ty
            in
            let* assign_rhs =
              disambiguate_process_expr assign_desc.assign_rhs expected_type disam_tbl
            in
            
            let* () = Rewriter.Logs.debug (fun printers m ->
                m "process_stmt: disam_assign_rhs: %a" printers.pr_expr
                  assign_rhs) in
            
            let assign_desc =
              Stmt.{ assign_desc with assign_lhs; assign_rhs }
            in
            Rewriter.return (Stmt.Assign assign_desc, disam_tbl)
      end
    | Bind bind_desc ->
      let* bind_lhs, _ =
          Rewriter.List.fold_right bind_desc.bind_lhs ~init:([], [])
            ~f:(fun orig_qual_ident (assign_lhs, var_decls_lhs) ->
                let+ qual_ident, var_decl = get_assign_lhs orig_qual_ident ~is_ghost_cmd:true ~is_init:false in
                qual_ident :: assign_lhs, var_decl :: var_decls_lhs
            )
      in
      let+ spec_form =
        disambiguate_process_expr bind_desc.bind_rhs.spec_form (Type.any |> Type.set_ghost true)
          disam_tbl
      in
      let bind_rhs = { bind_desc.bind_rhs with spec_form } in
      let bind_desc = Stmt.{ bind_lhs; bind_rhs } in
      Stmt.Bind bind_desc, disam_tbl
    | FieldWrite fw_desc ->
      let* field_write_field, symbol =
        Rewriter.resolve_and_find fw_desc.field_write_field
      in
      let* symbol = Rewriter.Symbol.reify symbol in
      let field_type = match symbol with
        | FieldDef { field_type = App (Fld, [ field_type ], _); _ }  ->
          field_type
        | _ -> Error.type_error (QualIdent.to_loc fw_desc.field_write_field) "Expected field"
      in
      let* is_field_an_ra = ProgUtils.is_ra_type field_type in
      let _ = if is_field_an_ra then
          Error.type_error stmt_loc
            (Printf.sprintf !"Cannot assign directly to field %{QualIdent}, whose value is a resource algebra (RA) element; use a frame-preserving update ('fpu') instead" fw_desc.field_write_field)
      in
      let* field_write_ref =
        disambiguate_process_expr fw_desc.field_write_ref Type.ref
          disam_tbl
      in
      let+ field_write_val =
        disambiguate_process_expr fw_desc.field_write_val field_type
          disam_tbl
      in
      Stmt.FieldWrite { field_write_ref; field_write_field; field_write_val }, disam_tbl
      
    | FieldRead fr_desc -> 
      let* fr_var_qual_ident, var_decl = get_assign_lhs fr_desc.field_read_lhs ~is_init:fr_desc.field_read_is_init in
      let* fr_type =
        ProcessTypeExpr.expand_type_expr var_decl.var_type
      in
      let* field_read_ref, field_read_field, field_type, symbol =
        disambiguate_process_field_read fr_desc.field_read_ref fr_desc.field_read_field disam_tbl
      in
      begin match symbol with
        | DestrDef { destr_return_type ; _ } ->
        
          let rhs_loc = Loc.merge (Expr.to_loc field_read_ref) (QualIdent.to_loc field_read_field) in
          let assign_rhs = Expr.mk_app ~loc:rhs_loc ~typ:destr_return_type (DataDestr fr_desc.field_read_field) [fr_desc.field_read_ref] in 
          let assign_desc =
            Stmt.{
              assign_lhs = [fr_desc.field_read_lhs];
              assign_rhs;
              assign_is_init = fr_desc.field_read_is_init
            }
          in
          process_basic_stmt call_decl (Stmt.Assign assign_desc) stmt_loc disam_tbl
        | _ ->
          let+ _ = ProcessExpr.check_and_set (Expr.mk_var ~typ:fr_type fr_var_qual_ident) fr_type field_type (field_type |> Type.set_ghost_to fr_type) in
          let field_read_desc =
            Stmt.
              {
                fr_desc with
                field_read_lhs = fr_var_qual_ident;
                field_read_field;
                field_read_ref;
              }
          in
          (Stmt.FieldRead field_read_desc, disam_tbl)
      end
    | Havoc hvc ->
      let+ havoc_var, _ = get_assign_lhs hvc.havoc_var ~is_init:hvc.havoc_is_init in
      Stmt.Havoc { hvc with havoc_var }, disam_tbl
    | Return expr ->
      if is_ghost_scope && Poly.(call_decl.Callable.call_decl_kind = Proc) then
        Error.type_error stmt_loc "Cannot return in a ghost block";

      let* expr = disambiguate_expr expr disam_tbl in
      let return_list = Expr.unfold_tuple expr in

      let+ return_list = ProcessExpr.process_callable_returns stmt_loc ~is_ghost_scope ~is_call:false call_decl return_list in
      let expr = Expr.mk_tuple ~loc:(Expr.to_loc expr) return_list in
      (Stmt.Return expr, disam_tbl)
    | Use use_desc ->
      let* use_name, symbol =
        let* id = disambiguate_ident use_desc.use_name disam_tbl in
        Rewriter.resolve_and_find id
      in
      let* symbol = Rewriter.Symbol.reify symbol in
      
      let pred_decl, pred_def =
        match symbol with
        | CallDef
            {
              call_decl = { call_decl_kind = Pred; _ } as pred_decl;
              call_def = FuncDef {func_body = pred_def}
            } ->
          pred_decl, pred_def
        | CallDef
            {
              call_decl =
                { call_decl_kind = Invariant; _ } as pred_decl;
              call_def = FuncDef {func_body = pred_def}
            } ->
          pred_decl, pred_def
        | _ ->
          Error.type_error stmt_loc
            ("Expected predicate or invariant identifier, but found "
             ^ QualIdent.to_string use_name)
      in


      
      let exists_vars =
        Option.value pred_def ~default:(Expr.mk_unit Loc.dummy)
        |> Expr.existential_vars_type
      in
      let find_type ident : type_expr Rewriter.t =
        let ty_opt = Map.fold exists_vars ~init:None ~f:(fun ~key ~data acc ->
            if Option.is_none acc
            && String.(Ident.name ident = Ident.name key)
            then Some data else acc)
        in
        match ty_opt with
        | Some ty -> 
          ProcessTypeExpr.process_type_expr ty
        | _ -> Error.type_error (Ident.to_loc ident)
                 (Printf.sprintf !"Could not find existential variable %{Ident} in %s %{QualIdent}" ident (Symbol.kind symbol) use_desc.use_name)
      in

      let* use_args =
        Rewriter.List.map use_desc.use_args ~f:(fun expr ->
            disambiguate_expr expr disam_tbl)
      in
      
      let* use_args =
        ProcessExpr.process_callable_args stmt_loc true pred_decl use_args
      in
      
      let+ use_witnesses_or_binds = 
        Rewriter.List.map use_desc.use_witnesses_or_binds ~f:(fun (i, e) ->
            match use_desc.use_kind with
            | Fold ->
              let* ty = find_type i in
              let+ e = disambiguate_process_expr e (ty |> Type.set_ghost true) disam_tbl in
              (i, e)
            | Unfold ->
              match e with
              | App (Var qual_ident, [], _) when QualIdent.is_local qual_ident ->
                let* ty =
                  find_type (QualIdent.unqualify qual_ident)
                in
                let+ ie = disambiguate_process_expr (Expr.mk_var ~typ:(Type.mk_any (Ident.to_loc i)) (QualIdent.from_ident i)) (ty |> Type.set_ghost true) disam_tbl in
                (Expr.to_ident ie, e) 
              | _ -> Error.type_error (Expr.to_loc e) "Expected local identifier"
          ) 
      in
      
      ( Stmt.Use { use_desc with use_name; use_args; use_witnesses_or_binds },
        disam_tbl )
    | New new_desc ->
      let* new_qual_ident, var_decl = get_assign_lhs new_desc.new_lhs ~is_init:new_desc.new_is_init in
      let* var_type_expanded =
        ProcessTypeExpr.expand_type_expr var_decl.var_type
      in
      
      if Type.equal var_type_expanded Type.ref then
        let process_field_init (field_name, expr_opt) =
          let* field_name, symbol =
            Rewriter.resolve_and_find field_name
          in
          let* field_type =
            Rewriter.Symbol.reify_field_type stmt_loc symbol
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
        
        let new_desc = Stmt.{ new_desc with new_lhs = new_qual_ident; new_args } in
        
        (Stmt.New new_desc, disam_tbl)
      else
        type_mismatch_error stmt_loc Type.ref var_decl.var_type
      (* The following constructs are not expected here because the parser stores these commands as Assign stmts.
         The job of this function is to intercept the Assign stmts with the specific expressions on the RHS, and then transform
         them to the appropriate construct, ie Call, New, BindAU, OpenAU, AbortAU, CommitAU etc.

         This function is not expected to go over these parts of the AST again. If the following constructs are
         discovered by this function, then something unexpected has happened. *)
      (* Now that we call process_symbol on arbitrarily AST elements, we need to deal with these constructs too *)
    | Call call_desc -> (        
        let* call_lhs, var_decls_lhs =
          Rewriter.List.fold_right call_desc.call_lhs ~init:([], [])
            ~f:(fun orig_qual_ident (assign_lhs, var_decls_lhs) ->
                let+ qual_ident, var_decl = get_assign_lhs orig_qual_ident ~is_init:call_desc.call_is_init in
                qual_ident :: assign_lhs, var_decl :: var_decls_lhs
            )
        in
        let* call_lhs_expr =
          Rewriter.List.map2_exn call_lhs var_decls_lhs ~f:(fun qual_ident var_decl ->
              let+ typ = ProcessTypeExpr.expand_type_expr var_decl.var_type in
              Expr.mk_var ~typ qual_ident)
        in
        
        let* call_decl = Rewriter.find_and_reify_callable call_desc.call_name |+> fun c -> c.call_decl in
        let* call_lhs_expr = ProcessExpr.process_callable_returns stmt_loc ~is_ghost_scope ~is_call:true call_decl call_lhs_expr in
        let is_ghost =
          is_ghost_scope ||
          match call_decl.call_decl_kind with
          | Lemma -> true 
          | Func -> 
            List.for_all call_lhs_expr ~f:(fun e -> e |> Expr.to_type |> Type.is_ghost)
          | _ -> false
        in
        let* _ = Rewriter.enter_ghost is_ghost in
        let* call_expr =
          Expr.App
            ( Var call_desc.call_name,
              call_desc.call_args,
              Expr.mk_attr stmt_loc Type.any )
          |> fun expr ->
          disambiguate_process_expr expr (Type.any |> Type.set_ghost is_ghost) disam_tbl ~allow_proc_call:true
        in
        let+ _ = Rewriter.exit_ghost in

        match call_expr with
        | App (Var call_name, call_args, _expr_attr) ->
          let call_desc =
            { call_desc with
              call_lhs;
              call_name;
              call_args;
            }
          in          
          (Stmt.Call call_desc, disam_tbl)
        | _ -> failwith "Unexpected error during type checking.")
    | AUAction _au_action_kind ->
      internal_error stmt_loc
        "Did not expect AU action stmts in AST at this stage."
    | Fpu fpu_desc ->
      let open Rewriter.Syntax in
      (* Process reference expression as ghost ref *)
      let* fpu_ref = disambiguate_process_expr fpu_desc.fpu_ref (Type.ref |> Type.set_ghost true) disam_tbl in

      (* Resolve field and check it is a ghost Fld field with element type *)
      let* fpu_field, symbol = Rewriter.resolve_and_find fpu_desc.fpu_field in
      let* symbol = Rewriter.Symbol.reify symbol in
      let* given_type =
      match symbol with
      | FieldDef field_decl -> (
        match field_decl.field_type with
        | App (Fld, [ elem_ty ], _) ->
          if not field_decl.field_is_ghost then
            Error.type_error (QualIdent.to_loc fpu_desc.fpu_field)
            "Frame-preserving updates are only allowed on ghost fields"
          else Rewriter.return elem_ty
        | _ ->
          Error.type_error (QualIdent.to_loc fpu_desc.fpu_field)
            "Expected field identifier")
      | _ ->
        Error.type_error (QualIdent.to_loc fpu_desc.fpu_field)
          "Expected field identifier"
      in

      (* Process optional old value and mandatory new value at the field element type *)
      let* fpu_old_val =
      Rewriter.Option.map fpu_desc.fpu_old_val ~f:(fun e ->
        disambiguate_process_expr e given_type disam_tbl)
      in
      let+ fpu_new_val = disambiguate_process_expr fpu_desc.fpu_new_val given_type disam_tbl in

      ( Stmt.Fpu
        {
        fpu_ref;
        fpu_field;
        fpu_old_val;
        fpu_new_val;
        },
      disam_tbl )
    | BasicStmtExt (stmt_ext, expr_list)  ->
      let* ext_hooks = Rewriter.current_ext_hooks in
        ext_hooks.type_check_basic_stmt call_decl stmt_ext expr_list stmt_loc disam_tbl
          {
            ExtApi.get_assign_lhs = get_assign_lhs;
            expand_type_expr = ProcessTypeExpr.expand_type_expr;
            disambiguate_process_expr;
            type_mismatch_error;
            disam_tbl_add_var_decl = DisambiguationTbl.add_var_decl;
            process_symbol = !Rewriter.process_symbol_ref;
            process_stmt = !Rewriter.process_stmt_ref;
          }

  let process_stmt ?(new_scope = true) call_decl
      (stmt : Stmt.t) (disam_tbl : DisambiguationTbl.t) :
    (Stmt.t * DisambiguationTbl.t) Rewriter.t =
    let rec process_stmt ?(new_scope = true) stmt disam_tbl =
      let open Rewriter.Syntax in
      let* () = Rewriter.Logs.debug (fun printers m -> m "process_stmt: %a" printers.pr_stmt stmt) in
      let* is_ghost_scope = Rewriter.is_ghost_scope in
      let+ stmt_desc, disam_tbl =
        match stmt.Stmt.stmt_desc with
        | Basic basic_stmt ->
          let+ basic_stmt, disam_tbl' =
            process_basic_stmt call_decl basic_stmt (Stmt.to_loc stmt) disam_tbl
          in
          (Stmt.Basic basic_stmt, disam_tbl')
        | Block block_desc ->
            let* () = Rewriter.enter_block block_desc in
            let disam_tbl =
              if new_scope then DisambiguationTbl.push disam_tbl else disam_tbl
            in

            let* disam_tbl, stmt_list =
              Rewriter.List.fold_map block_desc.block_body ~init:disam_tbl
                ~f:(fun disam_tbl stmt ->
                  let+ stmt, disam_tbl = process_stmt stmt disam_tbl in
                  (disam_tbl, stmt))
            in

            let disam_tbl =
              if new_scope then DisambiguationTbl.pop disam_tbl else disam_tbl
            in
            let+ () = Rewriter.exit_block in

            (Stmt.Block { block_desc with block_body = stmt_list }, disam_tbl)
        | Loop loop_desc ->
            let* loop_contract =
              Rewriter.List.map loop_desc.loop_contract
                ~f:(process_stmt_spec disam_tbl)
            in

            let* loop_contract_ext =
              let* ext_hooks = Rewriter.current_ext_hooks in
              Rewriter.List.map loop_desc.loop_contract_ext
                ~f:(fun contract_ext ->
                    ext_hooks.type_check_contract_ext call_decl contract_ext (Stmt.to_loc stmt) disam_tbl
                      {
                        ExtApi.get_assign_lhs =
                          (fun ~is_init:_ ?is_ghost_cmd:_ qi _state ->
                             Error.internal_error (QualIdent.to_loc qi)
                               "assignments are not permitted in a contract clause");
                        expand_type_expr = ProcessTypeExpr.expand_type_expr;
                        disambiguate_process_expr;
                        type_mismatch_error;
                        disam_tbl_add_var_decl = DisambiguationTbl.add_var_decl;
                        process_symbol = !Rewriter.process_symbol_ref;
                        process_stmt =
                          (fun _call_decl stmt _disam_tbl ->
                             Error.internal_error (Stmt.to_loc stmt)
                               "statements are not permitted in a contract clause");
                      })
            in

            let disam_tbl = DisambiguationTbl.push disam_tbl in
            let* loop_prebody, disam_tbl =
              process_stmt loop_desc.loop_prebody disam_tbl
            in
            let disam_tbl = DisambiguationTbl.pop disam_tbl in

            let* loop_test =
              disambiguate_process_expr loop_desc.loop_test (Type.bool |> Type.set_ghost is_ghost_scope) disam_tbl
            in

            let disam_tbl = DisambiguationTbl.push disam_tbl in
            let+ loop_postbody, disam_tbl =
              process_stmt loop_desc.loop_postbody disam_tbl
            in
            let disam_tbl = DisambiguationTbl.pop disam_tbl in

            (* Actually think about what variables need to be collected in `locals`. What if same variable is declared in multiple scopes in a callable, do all of them go in the `call_decl.call_decl_locals`? TW: I would say yes, unless you already have that information in the SymbolTable and always lookup locals through that. *)
            let (loop_desc : Stmt.loop_desc) =
              { loop_contract; loop_contract_ext; loop_prebody; loop_test; loop_postbody }
            in

            (Stmt.Loop loop_desc, disam_tbl)
        | Cond cond_desc ->
            let* cond_test =
              Rewriter.Option.map
                ~f:(fun test ->
                    disambiguate_process_expr test (Type.bool |> Type.set_ghost is_ghost_scope) disam_tbl)
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
        | StmtExt stmt_ext ->
            let* ext_hooks = Rewriter.current_ext_hooks in
            ext_hooks.type_check_stmt_ext call_decl stmt_ext (Stmt.to_loc stmt) disam_tbl
              {
                ExtApi.get_assign_lhs =
                  (fun ~is_init:_ ?is_ghost_cmd:_ qi _state ->
                     Error.internal_error (QualIdent.to_loc qi)
                       "assignments are not permitted directly in a top-level statement extension");
                expand_type_expr = ProcessTypeExpr.expand_type_expr;
                disambiguate_process_expr;
                type_mismatch_error;
                disam_tbl_add_var_decl = DisambiguationTbl.add_var_decl;
                process_symbol = !Rewriter.process_symbol_ref;
                process_stmt = (fun _call_decl stmt disam_tbl -> process_stmt stmt disam_tbl);
              }
      in

      (Stmt.{ stmt_desc; stmt_loc = stmt.stmt_loc }, disam_tbl)
    in

    process_stmt ~new_scope stmt disam_tbl

  let process_callable (callable : Callable.t) : Module.symbol Rewriter.t =
    let open Rewriter.Syntax in
    let* () = Rewriter.Logs.debug (fun printers m ->
        m "Typing.process_callable: Start Processing callable: %a" printers.pr_callable
          callable) in
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

    let* ext_hooks = Rewriter.current_ext_hooks in

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

    let call_decl_for_ext =
      { call_decl with call_decl_formals; call_decl_returns; call_decl_locals }
    in
    let* call_decl_contract_ext =
      Rewriter.List.map call_decl.call_decl_contract_ext
        ~f:(fun contract_ext ->
            ext_hooks.type_check_contract_ext call_decl_for_ext contract_ext
              call_decl.call_decl_loc disam_tbl
              {
                ExtApi.get_assign_lhs =
                  (fun ~is_init:_ ?is_ghost_cmd:_ qi _state ->
                     Error.internal_error (QualIdent.to_loc qi)
                       "assignments are not permitted in a contract clause");
                expand_type_expr = ProcessTypeExpr.expand_type_expr;
                disambiguate_process_expr;
                type_mismatch_error;
                disam_tbl_add_var_decl = DisambiguationTbl.add_var_decl;
                process_symbol = !Rewriter.process_symbol_ref;
                process_stmt =
                  (fun _call_decl stmt _disam_tbl ->
                     Error.internal_error (Stmt.to_loc stmt)
                       "statements are not permitted in a contract clause");
              })
    in

    Logs.debug (fun m -> m "done processing pre/post cond");
    let call_decl =
      {
        call_decl with
        call_decl_formals;
        call_decl_returns;
        call_decl_locals;
        call_decl_precond;
        call_decl_postcond;
        call_decl_contract_ext;
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
                  process_stmt ~new_scope:false call_decl stmt
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
                Rewriter.resolve
                  (QualIdent.from_ident type_def.type_def_name)
              in

              let _ =
                if List.is_empty variant_decl_list
                then Error.error (Type.to_loc tp_expr) "data types must have at least one constructor"
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
                            Error.error (Ident.to_loc var_arg.var_name)
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
                Rewriter.resolve
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
            Rewriter.resolve_and_find qual_ident
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
    let _ =
      if not var.var_decl.var_const
      then Error.type_error var.var_decl.var_loc "Modules and interfaces cannot have var members"
    in
    let* var_decl = ProcessTypeExpr.process_var_decl var.var_decl in
    let+ var_init =
      Rewriter.Option.map var.var_init ~f:(fun expr ->
          ProcessExpr.process_expr expr var_decl.var_type)
    in
    let var_type =
      var_init |> Option.map ~f:Expr.to_type |> Option.value ~default:var_decl.var_type
    in
    let _ = if Type.equal var_type Type.any then
        Error.error var_decl.var_loc
          @@ Printf.sprintf "Type annotation missing for variable %s"
            (Ident.to_string var_decl.var_name)
    in
    let var_is_free = var.var_is_free in
    let (var : Stmt.var_def) = { var_decl = { var_decl with var_type }; var_init; var_is_free } in
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
              let* () = Rewriter.Logs.debug (fun printers m -> m "orig: %a" printers.pr_type _orig_tp) in
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
                       %{QualIdent}. It cannot be redefined"
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
                       %{QualIdent}"
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
                     as %{Ident} in interface %{QualIdent}"
                   (Symbol.kind symbol) ident ident interface_ident)
        in

        if
          Poly.(
            call_def.call_decl.call_decl_kind
            <> orig_call_def.call_decl.call_decl_kind)
        then
          Error.type_error loc
            (Printf.sprintf
               !"Cannot redeclare %s %{Ident} from %{QualIdent} as %s"
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
                     %{Ident} in interface %{QualIdent}"
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
                     %{Ident} in interface %{QualIdent}"
                   (Symbol.kind symbol) ident ident interface_ident)
          in
          match (call_def.call_def, orig_call_def.call_def) with
          | ProcDef { proc_body = Some _; _ }, ProcDef { proc_body = Some _; _ }
          | FuncDef { func_body = Some _; _ }, FuncDef { func_body = Some _; _ }
            ->
              Error.type_error loc
                (Printf.sprintf
                   !"%s %{Ident} was already defined in interface \
                     %{QualIdent}. It cannot be redefined"
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
                 !"%s %{Ident} cannot have module parameters"
                 (Symbol.kind symbol |> String.capitalize)
                 ident)
          else
            match orig_mod_inst.mod_inst_def with
            | Some _ ->
                Error.type_error loc
                  (Printf.sprintf
                     !"%s %{Ident} was already defined in interface \
                       %{QualIdent}. It cannot be redefined"
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
        else
          let* mod_inst_def = Rewriter.find_and_reify_module mod_inst.mod_inst_type in
          if not @@ Set.mem mod_inst_def.mod_decl.mod_decl_interfaces orig_mod_inst.mod_inst_type then
            let _ = Logs.debug (fun m -> m !"%{QualIdent} %{QualIdent}" mod_inst.mod_inst_type orig_mod_inst.mod_inst_type) in
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
                     %{QualIdent}. It cannot be redefined"
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
    | ModDef mod_def, ModDef _orig_mod_def ->
      (* If LHS is free, then we are checking an inherited module against itself, which is OK. *)
      if is_free mod_def.mod_decl.mod_decl_status then Rewriter.return () else
      (* Otherwise, RHS is being redefined, which is not OK. *)
        Error.type_error loc
          (Printf.sprintf
             !"%s %{Ident} was already defined in interface %{QualIdent}. It \
               cannot be redefined"
             (Symbol.kind symbol |> String.capitalize)
             ident interface_ident)
    | _ ->
        Error.type_error loc
          (Printf.sprintf
             !"Cannot redeclare %s %{Ident} from interface %{QualIdent} as %s"
             (Symbol.kind orig_symbol) ident interface_ident
             (Symbol.kind symbol))

  (** Check that module `mod_ident` (M) implements interface `int_ident` (I) *)
  let check_module_type mod_ident int_ident =
    let open Rewriter.Syntax in
    (* Get qualified idents and symbols of M and I *)
    let+ qual_mod_ident, mod_symbol =
      Rewriter.resolve_and_find mod_ident
    and+ qual_int_ident, int_symbol =
      Rewriter.resolve_and_find int_ident
    in
    (* Extract all interfaces implemented by M and check whether it is fully instantiated *)
    let interfaces, mod_is_instance =
      Rewriter.Symbol.extract mod_symbol ~f:(fun is_instance subst -> function
        | Ast.Module.ModDef mod_def ->
            (*Set.map (module QualIdent) mod_def.mod_decl.mod_decl_interfaces ~f:subst*)
          mod_def.mod_decl.mod_decl_interfaces,
          List.is_empty mod_def.mod_decl.mod_decl_formals || is_instance
        | _ -> Set.empty (module QualIdent), true)
    in
    (* Check whether I is fully instantiated *)
    let int_is_instance =
      Rewriter.Symbol.extract int_symbol ~f:(fun is_instance _subst -> function
        | Ast.Module.ModDef mod_def ->
            List.is_empty mod_def.mod_decl.mod_decl_formals || is_instance
        | _ -> true)
    in
    (* Check if I is one of M's interfaces *)
    if
      not
        (QualIdent.(qual_mod_ident = qual_int_ident)
        || Set.mem interfaces qual_int_ident)
    then
      Error.type_error
        (QualIdent.to_loc mod_ident)
        (Printf.sprintf
           !"%s %{QualIdent} does not implement interface %{QualIdent}"
           (Symbol.kind (Rewriter.Symbol.orig_symbol mod_symbol) |> String.capitalize)
           mod_ident int_ident)
    else if
      (* Make sure that I is the type of M itself rather than the expected type
         of the module obtained by instantiating *)
      int_is_instance && not mod_is_instance
    then
      Error.type_error
        (QualIdent.to_loc mod_ident)
        (Printf.sprintf
           !"%s %{QualIdent} first needs to be instantiated to obtain a module with interface %{QualIdent}"
           (Symbol.kind (Rewriter.Symbol.orig_symbol mod_symbol) |> String.capitalize)
           mod_ident int_ident)
      

  let rec process_module (m : Module.t) : Module.t Rewriter.t =
    let open Rewriter.Syntax in
    let _ =
      Logs.info (fun mm ->
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
          let* symbol_def =
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
                (* A functor application `module M : I = F[args]` *)
                (* Get symbol of I *)
                let* mod_inst_type =
                  Rewriter.resolve mod_inst.mod_inst_type
                in
                (* Resolve the functor `F` and pair up its formals with `args`,
                   wrapping any bare-type argument (e.g. `M[Int]`) into a
                   synthesized module implementing the formal's rep-typed
                   interface (see `ProgUtils.intros_rep_module`). This must
                   happen *before* `declare_symbol` below, since
                   `SymbolTbl.add_symbol` resolves every argument to an
                   already-existing module to build the instance's
                   substitution. *)
                let* mod_inst_def, to_check =
                  match mod_inst.mod_inst_def with
                  | None -> Rewriter.return (None, [])
                  | Some (mod_inst_func, mod_inst_args) ->
                      (* Get qualified name of F and its symbol *)
                      let* qual_functor_ident, functor_symbol =
                        Rewriter.resolve_and_find
                          mod_inst_func
                      in
                      (* Get formal parameters of F *)
                      let formals =
                        Rewriter.Symbol.extract functor_symbol ~f:(fun is_instance subst ->
                          function
                          | Ast.Module.ModDef mod_def when not is_instance ->
                              List.map mod_def.mod_decl.mod_decl_formals
                                ~f:(fun formal -> (formal, subst formal.mod_inst_type))
                          | _ -> [])
                      in
                      (* Pair up `args` and formals *)
                      let* args_and_formals =
                        match List.zip mod_inst_args formals with
                        | Ok res -> Rewriter.return res
                        | Unequal_lengths ->
                            arg_mismatch_error "Module" (QualIdent.to_loc mod_inst_func) (Type.Var mod_inst_func)
                              (List.length formals)
                      in
                      let+ resolved_args =
                        Rewriter.List.map args_and_formals
                          ~f:(fun (arg, (formal, formal_iface)) ->
                            match arg with
                            | Module.ModArg qi -> Rewriter.return (qi, formal_iface)
                            | Module.TypeArg tp -> (
                                let* rep = ProgUtils.resolve_rep_ident formal_iface in
                                match rep with
                                | None ->
                                    Error.type_error (Type.to_loc tp)
                                      (Printf.sprintf
                                         !"Cannot pass a type as argument for parameter \
                                           %{Ident}: interface %{QualIdent} does not \
                                           declare a rep type"
                                         formal.mod_inst_name formal_iface)
                                | Some (interface_qual_ident, rep_ident) ->
                                    let* insert_scope, reference_scope =
                                      ProgUtils.find_insertion_scope_for_types [ tp ]
                                    in
                                    let+ qi =
                                      ProgUtils.get_or_intros_rep_module
                                        ~loc:(Type.to_loc tp)
                                        ~f:!(Rewriter.process_symbol_ref)
                                        ~insert_scope ~reference_scope
                                        ~interface_qual_ident ~rep_ident tp
                                    in
                                    (qi, formal_iface)))
                      in
                      ( Some
                          ( qual_functor_ident,
                            List.map resolved_args ~f:(fun (qi, _) -> Module.ModArg qi) ),
                        (qual_functor_ident, mod_inst.mod_inst_type) :: resolved_args )
                in
                let symbol = Module.ModInst { mod_inst with mod_inst_type; mod_inst_def } in
                (* Only instantiations (`mod_inst_def = Some _`) are declared here;
                   abstract module parameters (`mod_inst_def = None`) are already
                   declared by the pre-declare pass above. *)
                let* _ =
                  match mod_inst.mod_inst_def with
                  | None -> Rewriter.return ()
                  | Some _ -> Rewriter.declare_symbol symbol
                in
                (* Check that `args` satisfy module types of formals *)
                let+ _ =
                  Rewriter.List.iter to_check ~f:(fun (m, i) ->
                      check_module_type m i)
                in
                symbol
          in
          let* () = Rewriter.Logs.debug (fun printers mm ->
              mm
                "Processing module %a: symbol: %a"
                Ident.pr (Symbol.to_name (ModDef m))
                printers.pr_symbol symbol_def) in
          let+ _ = Rewriter.set_symbol symbol_def in
          Module.SymbolDef symbol_def
      | Import import ->
        (* Handled by symbol table *)
            let* () =
              if not import.import_all then Rewriter.return ()
              else
                let* generic_functor = ProgUtils.resolve_generic_functor import.import_name in
                match generic_functor with
                | None -> Rewriter.return ()
                | Some _ ->
                    let import_name_str = QualIdent.to_string import.import_name in
                    Error.type_error import.import_loc
                      (Printf.sprintf
                         "Cannot import all members of `%s` because it is a generic functor \
                          that has not been instantiated; write `import %s[...]._` after an \
                          explicit instantiation"
                         import_name_str import_name_str)
            in
            let* _ = Rewriter.import import in
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

        Rewriter.resolve 
          (QualIdent.from_ident (Symbol.to_name (ModDef m)))
    in
    (* merge symbol definitions from parent interface with those from current module
     * so that the dependency order between symbols is preserved *)
    let merge_defs parent_ident parent_mod_def mod_def =
      let formals =
        List.fold_left ~init:(Set.empty (module Ident))
          ~f:(fun acc -> function
              | SymbolDef (ModInst mod_inst) ->  Set.add acc mod_inst.mod_inst_name
              | _ -> acc)
          mod_def_formals
      in
      (*let _parent_defined_symbols = get_defined_symbols parent_mod_def in*)
      let rec merge_defs (merged, to_check, seen) = function
        | [], mod_def -> (List.rev_append merged mod_def, to_check)
        | Module.Import _ :: parent_mod_def, mod_def ->
            merge_defs (merged, to_check, seen) (parent_mod_def, mod_def)
        | Module.SymbolDef (ConstrDef _ | DestrDef _)  :: parent_mod_def, mod_def
        | parent_mod_def, Module.SymbolDef (ConstrDef _ | DestrDef _) :: mod_def
          ->
            merge_defs (merged, to_check, seen) (parent_mod_def, mod_def)
        | Module.SymbolDef parent_symbol :: parent_mod_def, mod_def -> (
            let parent_symbol_ident = Symbol.to_name parent_symbol in
            let annotate_error_msg = function
              | Module.CallDef ({ call_decl; _ } as call) as symbol ->
                let annotate_spec spec =
                  let error =
                    ( Error.RelatedLoc,
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
            if Set.mem formals parent_symbol_ident then
              (* case: parent_symbol is being abstracted over *)
              merge_defs
                ( merged,
                  Map.add_exn to_check ~key:parent_symbol_ident
                    ~data:parent_symbol,
                  seen )
                (parent_mod_def, mod_def)
            else if not (Set.mem defined_symbols parent_symbol_ident)
               && (Set.is_empty seen || List.is_empty mod_def)
            then
              (* case: parent_symbol should be inherited now *)
              let _ = Logs.debug (fun m -> m !"Inheriting symbol %{Ident}" parent_symbol_ident) in
              let parent_symbol =
                match parent_symbol with
                | CallDef call when not @@ Callable.is_abstract call ->
                  Logs.debug (fun m -> m !"Making %{Ident} free." (Callable.to_ident call));
                  Module.CallDef (Callable.set_machine_free call)
                | CallDef
                    ({ call_decl = { call_decl_kind = Lemma; _ }; _ } as call)
                  when Callable.is_abstract call
                       && not m.mod_decl.mod_decl_is_interface ->
                  let loc = m.mod_decl.mod_decl_loc in
                  (* Keep 'auto' flag for everything but RA associativity axioms *)
                  let auto =
                    call.call_decl.call_decl_is_auto &&
                    String.(call.call_decl.call_decl_name |> Ident.name <> "compAssoc")
                  in
                  let call =
                    {
                      Callable.call_decl = { call.call_decl with call_decl_is_auto = auto };
                      call_def =
                        ProcDef { proc_body = Some (Stmt.mk_skip ~loc) };
                    }
                  in
                  let call =
                    if is_free m.mod_decl.mod_decl_status
                    then Callable.set_machine_free call
                    else call
                  in
                  annotate_error_msg (CallDef call)
                | ModDef mod_def -> ModDef (Module.set_machine_free mod_def)
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
                      (Module.SymbolDef symbol :: merged, to_check, Set.remove seen symbol_ident)
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
              | [] -> assert false
          )
      in
      merge_defs
        ([], Map.empty (module Ident), Set.empty (module Ident))
        (parent_mod_def, mod_def)
    in

    (* Compute symbols that are inherited from parent interface, respectively, that need to be checked against the parent interface *)
    let* ( mod_decl_returns,
           mod_decl_interfaces,
           interface_ident,
           interface_formals,
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
              Rewriter.resolve_and_find mid
            in
            let interface_symbol =
              Rewriter.Symbol.extend_subst
                (qual_interface_ident, QualIdent.to_list mod_qual_ident)
                interface_symbol
            in

            let* interface_symbol = Rewriter.Symbol.reify interface_symbol in
            let* () = Rewriter.Logs.debug (fun printers mm ->
                mm
                  !"Typing.process_module: %{Ident}: checking return type \
                    %a: reified; \n\
                   \ qual_interface_ident: %{QualIdent} \n\
                   \ mid: %{QualIdent}"
                  (Symbol.to_name (ModDef m))
                  printers.pr_symbol interface_symbol qual_interface_ident mid) in
            Rewriter.return (qual_interface_ident, mid, interface_symbol))
      in
      match interface_opt with
      | Some (qual_interface_ident, interface_ident, ModDef interface) ->
        ( Some qual_interface_ident,
          Set.add interface.mod_decl.mod_decl_interfaces qual_interface_ident,
          interface_ident,
          Some interface.mod_decl.mod_decl_formals,
          merge_defs qual_interface_ident interface.mod_def m.mod_def )
      | _ ->
          let mod_ident = QualIdent.from_ident m.mod_decl.mod_decl_name in
          let interfaces =
            if is_root then m.mod_decl.mod_decl_interfaces
            else Set.add m.mod_decl.mod_decl_interfaces mod_qual_ident
          in
          (None, interfaces, mod_ident, None, (m.mod_def, Map.empty (module Ident)))
    in

    (*let inherited_symbols = List.rev inherited_symbols in*)
    let mod_def = mod_def_formals @ merged_symbols in
    let _ = Logs.info (fun mm -> mm !"Merged in %{Ident}" (Symbol.to_name (ModDef m))) in
    let _ = List.iter ~f:(function SymbolDef symbol -> Logs.info (fun m -> m !"%{Ident}" (Symbol.to_name symbol)) | _ -> ()) mod_def in
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
              interface_ident
          in
          Rewriter.Symbol.extract interface_symbol ~f:(fun _ _ -> function
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
            Rewriter.resolve mod_inst.mod_inst_type
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

    (* Make sure that the module preserves the parameters of its interface *)
    let _ =
      let interface_formals = Option.value interface_formals ~default:[] in
      match interface_formals with
      | [] -> ()
      | _ ->
        let res =
          List.iter2 mod_decl.mod_decl_formals interface_formals
            ~f:(fun param oparam ->
              if
                Ident.(param.mod_inst_name <> oparam.mod_inst_name)
                || QualIdent.(param.mod_inst_type <> oparam.mod_inst_type)
              then
                Error.type_error param.mod_inst_loc
                  (Printf.sprintf
                     !"Parameter %{Ident} of %s %{Ident} does not match declaration of \
                       parameter %{Ident} of interface %{QualIdent}"
                     param.mod_inst_name (Symbol.kind (ModDef m)) mod_decl.mod_decl_name
                     oparam.mod_inst_name interface_ident))
        in
        match res with
        | Ok list -> list
        | Unequal_lengths ->
          param_mismatch_error "Interface" (Ident.to_loc mod_decl.mod_decl_name)
            (QualIdent.to_string interface_ident) (List.length interface_formals)
    in
    
    let* _ =
      Rewriter.List.iter mod_def ~f:(function
        | Module.SymbolDef (ModInst { mod_inst_def = Some _; _ }) | Module.Import _ -> Rewriter.return ()
        | Module.SymbolDef symbol -> Rewriter.declare_symbol symbol)
    in

    (* Check and rewrite all symbols *)
    let* mod_def = Rewriter.List.map merged_symbols ~f:process_instr in

    (* Check symbols against what is specified in the interface *)
    let* _ =
      Rewriter.List.iter mod_def ~f:(function
        | SymbolDef symbol ->
            let ident = Symbol.to_name symbol in
            Map.find symbols_to_check ident
            |> Rewriter.Option.iter ~f:(fun orig_symbol ->
                check_implements_symbol interface_ident symbol orig_symbol)
        | _ -> Rewriter.return ())
    in

    (* Check whether modules are indeed modules *)
    let* _ =
      if not mod_decl.mod_decl_is_interface then
        Rewriter.List.iter mod_def ~f:(function
          | Import _ -> Rewriter.return ()
          | SymbolDef symbol when not (Symbol.is_free symbol) -> (
              match symbol with
              | TypeDef { type_def_expr = None; _ }
              | ModInst { mod_inst_def = None; _ }
              | VarDef { var_decl = { var_const = true; _ }; var_init = None; _ }
              | CallDef { call_def = (ProcDef { proc_body = None } | FuncDef { func_body = None });
                          call_decl = { call_decl_status = NotFree; _ } } ->
                if Ident.(mod_decl.mod_decl_name = Predefs.prog_ident) then
                  Error.type_error (Symbol.to_loc symbol)
                    (Printf.sprintf
                       !"The %s %{Ident} cannot be abstract here. An abstract member can only be declared in an interface"
                       (Symbol.kind symbol)
                       (Symbol.to_name symbol))
                else 
                  Error.type_error mod_decl.mod_decl_loc
                    (Printf.sprintf
                       !"Module %{Ident} must be declared as an interface. The \
                         %s %{Ident} %b is still abstract"
                       mod_decl.mod_decl_name (Symbol.kind symbol) 
                       (Symbol.to_name symbol) (Symbol.is_free symbol))
              | ModInst { mod_inst_def = Some (mod_inst_func, _); mod_inst_is_interface = false; _ } ->
                let+ mod_inst_symbol =
                  Rewriter.find_and_reify mod_inst_func
                in
                (match mod_inst_symbol with
                | Module.ModDef mdef ->              
                  if mdef.mod_decl.mod_decl_is_interface then
                  Error.type_error (Symbol.to_loc symbol)
                    (Printf.sprintf
                       !"Module %{Ident} must be declared as an interface"
                       (Symbol.to_name symbol))
                | _ -> ())
              | _ -> Rewriter.return ())

          | _ -> Rewriter.return ())
      else Rewriter.return ()
    in
    let _ =
      Logs.debug (fun mm ->
          mm !"Done with processing module %{Ident}" (Symbol.to_name (ModDef m)))
    in
    let* () = Rewriter.Logs.debug (fun printers mm ->
          mm "%a" printers.pr_symbol (ModDef (Module.{ mod_decl; mod_def }))) in
    Rewriter.return (Module.{ mod_decl; mod_def })
end

(* Return variables are only meaningful once the callable has returned, so they must not
   occur in a `requires` clause -- only in `ensures` clauses. This is checked here, as a
   syntactic pass over the freshly parsed AST (rather than inside [ProcessCallable.process_callable]),
   because that function is also re-entered by the rewrite passes to type-check
   compiler-generated callables (e.g. skolem functions in [HeapsExplicitTrnsl]) whose
   preconditions may legitimately mention their own "return" variable by construction. *)
let rec check_return_vars_not_in_precond (m : Module.t) : unit =
  List.iter m.mod_def ~f:(function
    | Module.SymbolDef (CallDef callable) ->
        let call_decl = callable.call_decl in
        let return_qual_idents =
          List.map call_decl.call_decl_returns ~f:(fun var_decl ->
              QualIdent.from_ident var_decl.var_name)
          |> Set.of_list (module QualIdent)
        in
        List.iter call_decl.call_decl_precond ~f:(fun spec ->
            match
              Set.choose
                (Set.inter (Expr.symbols spec.spec_form) return_qual_idents)
            with
            | Some qual_ident ->
                Error.type_error (QualIdent.to_loc qual_ident)
                  (Printf.sprintf
                     !"Return variable %{QualIdent} cannot be used in a requires clause; it is only in scope in ensures clauses"
                     qual_ident)
            | None -> ())
    | Module.SymbolDef (ModDef nested_md) ->
        check_return_vars_not_in_precond nested_md
    | Module.SymbolDef (ModInst _ | TypeDef _ | ConstrDef _ | DestrDef _ | FieldDef _ | VarDef _)
    | Module.Import _ ->
        ())

let process_module ?(tbl = SymbolTbl.create ()) ?ext_hooks ?cli_config (m : Module.t) =
  assert (SymbolTbl.curr_is_root tbl);
  (* assert Ident.(m.mod_decl.mod_decl_name = QualIdent.to_ident (SymbolTbl.root_ident tbl)); *)
  let () = check_return_vars_not_in_precond m in
  let tbl, m =
    Rewriter.eval ?ext_hooks ?cli_config
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

let _ =
  Rewriter.process_symbol_ref := process_symbol;
  Rewriter.expand_type_expr_ref := ProcessTypeExpr.expand_type_expr;
  Rewriter.process_stmt_ref :=
    (fun call_decl stmt disam_tbl -> ProcessCallable.process_stmt call_decl stmt disam_tbl);
