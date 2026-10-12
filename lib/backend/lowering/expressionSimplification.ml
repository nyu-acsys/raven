(** Structural simplification after lowering calls and predicate bodies. *)

open Base
open Ast

let is_bool value = function
  | Expr.App (Bool actual, [], _) -> Bool.equal actual value
  | _ -> false

let rec simplify (expr : expr) : expr Rewriter.t =
  let open Rewriter.Syntax in
  let* expr =
    match expr with
    | Binder (binder, vars, triggers, body, attr) ->
        let* _ = Rewriter.add_locals vars in
        let+ body = simplify body in
        (* Trigger terms must retain their application structure. *)
        Expr.Binder (binder, vars, triggers, body, attr)
    | _ -> Rewriter.Expr.descend ~f:simplify expr
  in
  let loc = Expr.to_loc expr in
  let bool value = Rewriter.return (Expr.mk_bool ~loc value) in
  match expr with
  | App (DataTest tested, [ App (DataConstr constructor, _, _) ], _) ->
      bool (QualIdent.equal tested constructor)
  | App (DataDestr selector, [ App (DataConstr constructor, args, _) ], _) ->
      let+ selectors = ProgUtils.get_data_destrs_from_constr constructor in
      begin match List.findi selectors ~f:(fun _ qi -> QualIdent.equal qi selector) with
      | None -> expr
      | Some (index, _) -> Option.value (List.nth args index) ~default:expr
      end
  | App (TupleLookUp, [ App (Tuple, args, _); App (Int index, [], _) ], _) ->
      let result =
        let open Option.Let_syntax in
        let%bind index = Int64.to_int index in
        List.nth args index
      in
      Rewriter.return (Option.value result ~default:expr)
  | App (Eq, [ left; right ], _) when Expr.compare left right = 0 ->
      let* pure = ProgUtils.is_expr_pure left in
      if pure then bool true else Rewriter.return expr
  | App (Eq, [ App (DataConstr c1, args1, _); App (DataConstr c2, args2, _) ], _) ->
      if not (QualIdent.equal c1 c2) then bool false
      else
        let* equalities =
          Rewriter.List.map (List.zip_exn args1 args2) ~f:(fun (left, right) ->
              simplify (Expr.mk_eq ~loc left right))
        in
        simplify (Expr.mk_chained_and ~loc equalities)
  | App (Eq, [ App (Int left, [], _); App (Int right, [], _) ], _) ->
      bool (Int64.equal left right)
  | App (Eq, [ App (Bool left, [], _); App (Bool right, [], _) ], _) ->
      bool (Bool.equal left right)
  | App (Not, [ App (Bool value, [], _) ], _) -> bool (not value)
  | App (And, args, attr) -> simplify_connective Expr.And attr args
  | App (Or, args, attr) -> simplify_connective Expr.Or attr args
  | App (Impl, [ guard; body ], _) ->
      if is_bool false guard || is_bool true body then bool true
      else if is_bool true guard then Rewriter.return body
      else Rewriter.return expr
  | App (Ite, [ guard; left; right ], _) ->
      if is_bool true guard then Rewriter.return left
      else if is_bool false guard then Rewriter.return right
      else Rewriter.return expr
  | Binder ((Forall | Exists), _, _, body, _) when is_bool true body -> bool true
  | _ -> Rewriter.return expr

and simplify_connective operator attr args =
  let identity = match operator with Expr.And -> true | _ -> false in
  if List.exists args ~f:(is_bool (not identity)) then
    Rewriter.return (Expr.mk_bool ~loc:attr.Expr.expr_loc (not identity))
  else
    let args = List.filter args ~f:(fun arg -> not (is_bool identity arg)) in
    match args with
    | [] -> Rewriter.return (Expr.mk_bool ~loc:attr.Expr.expr_loc identity)
    | [ arg ] -> Rewriter.return arg
    | _ -> Rewriter.return (Expr.App (operator, args, attr))

let rewrite_callable (callable : Callable.t) =
  let open Rewriter.Syntax in
  let rewrite_specs specs =
    Rewriter.List.map specs ~f:(fun spec ->
        let+ spec_form = simplify spec.Stmt.spec_form in
        { spec with spec_form })
  in
  let call_decl = callable.call_decl in
  let* _ = Rewriter.add_call_decl_locals call_decl in
  let* call_decl_precond = rewrite_specs call_decl.call_decl_precond in
  let* call_decl_postcond = rewrite_specs call_decl.call_decl_postcond in
  let call_decl = { call_decl with call_decl_precond; call_decl_postcond } in
  let+ call_def =
    match callable.call_def with
    | FuncDef { func_body } ->
        let+ func_body = Rewriter.Option.map func_body ~f:simplify in
        Callable.FuncDef { func_body }
    | ProcDef { proc_body } ->
        let+ proc_body =
          Rewriter.Option.map proc_body ~f:(Rewriter.Stmt.rewrite_expressions ~f:simplify)
        in
        Callable.ProcDef { proc_body }
  in
  { Callable.call_decl; call_def }
