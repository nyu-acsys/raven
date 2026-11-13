(* Substitution avoids capture and respects rebinding. *)

open Base
open Raven
open Ast

let var name = Ident.make Util.Loc.dummy name 0
let decl name = Type.mk_var_decl ~loc:Util.Loc.dummy (var name) Type.int
let use name = Expr.from_var_decl (decl name)

let subst pairs =
  Map.of_alist_exn
    (module QualIdent)
    (List.map pairs ~f:(fun (x, e) -> (QualIdent.from_ident (var x), e)))

let bound = function
  | Expr.Binder (_, [ v ], _, body, _) -> (v, body)
  | _ -> failwith "expected a binder over one variable"

(* forall y :: x == y, with x := y: the bound y is renamed, so the substituted y stays free. *)
let () =
  let renamed, body =
    bound
      (Expr.alpha_renaming
         (Expr.mk_binder Forall [ decl "y" ] (Expr.mk_eq (use "x") (use "y")))
         (subst [ ("x", use "y") ]))
  in
  assert (not (Ident.equal renamed.var_name (var "y")));
  assert (Poly.equal body (Expr.mk_eq (use "y") (Expr.from_var_decl renamed)))

(* forall x :: x == z, with x := 1 and z := 2: the binder hides x, but z is replaced. *)
let () =
  let one = Expr.mk_int 1 and two = Expr.mk_int 2 in
  let kept, body =
    bound
      (Expr.alpha_renaming
         (Expr.mk_binder Forall [ decl "x" ] (Expr.mk_eq (use "x") (use "z")))
         (subst [ ("x", one); ("z", two) ]))
  in
  assert (Ident.equal kept.var_name (var "x"));
  assert (Poly.equal body (Expr.mk_eq (use "x") two))

(* Without a clash, a binder is kept as it is. *)
let () =
  let kept, _ =
    bound
      (Expr.alpha_renaming
         (Expr.mk_binder Forall [ decl "y" ] (Expr.mk_eq (use "x") (use "y")))
         (subst [ ("x", Expr.mk_int 3) ]))
  in
  assert (Ident.equal kept.var_name (var "y"))

(* Cloned sibling binders and their caller's free variables remain distinct. *)
let () =
  let original =
    Expr.mk_binder Exists [ decl "witness" ] (Expr.mk_eq (use "witness") (use "caller"))
  in
  let first, first_body = bound (Expr.freshen_bound_vars original) in
  let second, second_body = bound (Expr.freshen_bound_vars original) in
  assert (not (Ident.equal first.var_name second.var_name));
  assert (not (Ident.equal first.var_name (var "witness")));
  assert (Poly.equal first_body (Expr.mk_eq (Expr.from_var_decl first) (use "caller")));
  assert (Poly.equal second_body (Expr.mk_eq (Expr.from_var_decl second) (use "caller")))

(* A shadowing binder owns its body and triggers, while its sibling uses the outer one. *)
let () =
  let tag =
    Expr.mk_app ~typ:Type.int
      (Expr.Var (QualIdent.from_ident (var "tag")))
      [ use "witness" ]
  in
  let inner =
    Expr.mk_binder ~trigs:[ [ tag ] ] Forall
      [ decl "witness" ]
      (Expr.mk_eq (use "witness") (use "caller"))
  in
  let original =
    Expr.mk_binder Exists
      [ decl "witness" ]
      (Expr.mk_and [ Expr.mk_eq (use "witness") (use "caller"); inner ])
  in
  let outer, body = bound (Expr.freshen_bound_vars original) in
  match body with
  | Expr.App
      ( And,
        [ outside; Expr.Binder (Forall, [ inside ], [ [ trigger ] ], inside_body, _) ],
        _ ) ->
      assert (not (Ident.equal outer.var_name inside.var_name));
      assert (Poly.equal outside (Expr.mk_eq (Expr.from_var_decl outer) (use "caller")));
      assert (
        Poly.equal inside_body (Expr.mk_eq (Expr.from_var_decl inside) (use "caller")));
      let expected_trigger =
        Expr.mk_app ~typ:Type.int
          (Expr.Var (QualIdent.from_ident (var "tag")))
          [ Expr.from_var_decl inside ]
      in
      assert (Poly.equal trigger expected_trigger)
  | _ -> failwith "expected nested bound scopes"

(* Even unused declarations reserve their identities before a copy is refreshed. *)
let () =
  let unused =
    { (decl "unused") with var_name = Ident.make Util.Loc.dummy "unused" 500 }
  in
  let copied, _ =
    bound (Expr.freshen_bound_vars (Expr.mk_binder Exists [ unused ] (Expr.mk_bool true)))
  in
  assert (copied.var_name.ident_num > 500)

(* A renamed outer binder cannot collide with an unused nested declaration. *)
let () =
  let outer = decl "capture_unused_scope" in
  let unused =
    { outer with var_name = Ident.make Util.Loc.dummy "capture_unused_scope" 1 }
  in
  let original =
    Expr.mk_binder Forall [ outer ]
      (Expr.mk_binder Exists [ unused ]
         (Expr.mk_eq (use "source_unused_scope") (Expr.from_var_decl outer)))
  in
  let renamed, nested =
    bound
      (Expr.alpha_renaming original
         (subst [ ("source_unused_scope", Expr.from_var_decl outer) ]))
  in
  let kept, body = bound nested in
  assert (Ident.equal kept.var_name unused.var_name);
  assert (not (Ident.equal renamed.var_name kept.var_name));
  assert (
    Poly.equal body (Expr.mk_eq (Expr.from_var_decl outer) (Expr.from_var_decl renamed)))

(* Substitution images reserve their unused declarations too. *)
let () =
  let outer = decl "capture_image_scope" in
  let unused =
    { outer with var_name = Ident.make Util.Loc.dummy "capture_image_scope" 1 }
  in
  let image =
    Expr.mk_binder Exists [ unused ]
      (Expr.mk_eq (Expr.from_var_decl outer) (Expr.from_var_decl outer))
  in
  let original =
    Expr.mk_binder Forall [ outer ]
      (Expr.mk_var ~typ:Type.bool (QualIdent.from_ident (var "source_image_scope")))
  in
  let renamed, body =
    bound (Expr.alpha_renaming original (subst [ ("source_image_scope", image) ]))
  in
  assert (not (Ident.equal renamed.var_name unused.var_name));
  assert (phys_equal body image)

(* Empty substitutions do not traverse or rebuild the expression. *)
let () =
  let original =
    Expr.mk_binder Forall
      [ decl "unchanged" ]
      (Expr.mk_eq (use "unchanged") (use "caller"))
  in
  assert (
    phys_equal original (Expr.alpha_renaming original (Map.empty (module QualIdent))))

(* Replacing checked occurrences preserves their type metadata, including below roots. *)
let () =
  let alias = Type.mk_var (QualIdent.from_ident (var "IntegerAlias")) in
  let child = Expr.set_type (use "projection_source") alias in
  let image =
    Expr.mk_app ~typ:alias
      (Expr.DataDestr (QualIdent.from_ident (var "projection")))
      [ child ]
    |> fun expr -> Expr.set_type_annot expr (Some alias)
  in
  let occurrence = Expr.set_type_annot (use "typed_source") (Some Type.int) in
  let substitution = subst [ ("typed_source", image) ] in
  let check replacement =
    assert (Type.equal (Expr.to_type replacement) Type.int);
    assert (Option.equal Type.equal (Expr.to_type_annot replacement) (Some Type.int));
    match replacement with
    | Expr.App (DataDestr _, [ argument ], _) ->
        assert (phys_equal argument child);
        assert (Type.equal (Expr.to_type argument) alias)
    | _ -> failwith "expected the projection's structure"
  in
  check (Expr.alpha_renaming occurrence substitution);
  begin match
    Expr.alpha_renaming (Expr.mk_eq occurrence (Expr.mk_int 0)) substitution
  with
  | Expr.App (Eq, [ replacement; _ ], _) -> check replacement
  | _ -> failwith "expected the enclosing equality"
  end;
  assert (Type.equal (Expr.to_type image) alias)
