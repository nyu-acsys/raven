open Base
open Ast

(** Resolve aliases after module substitution, then merge coincident mask entries. *)
let resolve_mask (mask : Callable.mask) : (Callable.mask, 'a) Rewriter.t_ext =
  let open Rewriter.Syntax in
  let+ mask =
    Rewriter.List.map mask ~f:(fun (head, args) ->
        let+ name = Rewriter.resolve (Callable.mask_head_name head) in
        (Callable.map_mask_head head ~f:(fun _ -> name), args))
  in
  Callable.mask_canon mask

(* Longest prefix of [args] whose free variables are all among
   [formal_idents] -- walking stops at the first non-expressible argument,
   since a prefix can't skip past an unpinned link and still describe a
   meaningful narrower region. A variable bound by an enclosing quantifier
   (e.g. `exists nx :: ... is_queue(nx) ...`) is automatically treated as
   non-expressible here with no special-casing needed: it can never
   coincide with one of [formal_idents] (a different declaration's own
   formals, always a disjoint scope), so any argument built from it always
   truncates away on its own. *)
let truncate_to_formal_expressible (formal_idents : IdentSet.t) (args : Expr.t list) :
    Expr.t list =
  List.take_while args ~f:(fun arg ->
      Set.is_subset (Expr.local_vars arg) ~of_:formal_idents)

(* Walks an expression collecting every [Pred]/[Invariant] application
   (declaration, kind, arguments, and number of formals before `;`) reachable
   through [App]/[Binder] nesting -- the same traversal shape (and same [Pred] |
   [Invariant] filter) as [ProgUtils.expr_preds_mentioned], just
   additionally keeping each application's kind and arguments. *)
let rec inv_applications (expr : Expr.t) :
    ((QualIdent.t * Callable.call_kind * Expr.t list * int) list, 'a) Rewriter.t_ext =
  let open Rewriter.Syntax in
  match expr with
  | Expr.App (Expr.Var qual_ident, args, _) -> (
      let* qual_ident, (_, symbol, _) = Rewriter.resolve_and_find qual_ident in
      let* nested = Rewriter.List.map args ~f:inv_applications in
      let nested = List.concat nested in
      match symbol with
      | Module.CallDef
          {
            call_decl =
              { call_decl_kind = (Pred | Invariant) as kind; call_decl_formals; _ };
            _;
          } ->
          Rewriter.return
            ((qual_ident, kind, args, List.length call_decl_formals) :: nested)
      | _ -> Rewriter.return nested)
  | Expr.App (_, args, _) ->
      let+ nested = Rewriter.List.map args ~f:inv_applications in
      List.concat nested
  | Expr.Binder (_, _, _, body, _) -> inv_applications body

(* With [~explicit_only], retain every formal before `;` and drop the implicit
   arguments after it. Needs may approximate predicate dependencies this way;
   grants project only invariant implicit parameters below. *)
let expr_inv_applications ~explicit_only (expr : Expr.t) =
  let open Rewriter.Syntax in
  let+ apps = inv_applications expr in
  List.map apps ~f:(fun (qi, kind, args, n_formals) ->
      (qi, kind, if explicit_only then List.take args n_formals else args))

(* Invariant grants are indexed by every formal before `;`, including implicit
   ghost formals. Implicit parameters after `;` do not index invariant grants;
   predicate dependencies retain their implicit arguments. Opening credit does not
   supply ownership or determine the established instance's implicit arguments. *)
let expr_grant_applications expr =
  let open Rewriter.Syntax in
  let+ apps = inv_applications expr in
  List.map apps ~f:(fun (qi, kind, args, n_formals) ->
      ( qi,
        kind,
        match kind with Callable.Invariant -> List.take args n_formals | _ -> args ))
