(* Substitution avoids capture and respects rebinding. *)

open Base
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
