open Base
open Raven
open Ast

(* Identifiers hash by their names, also when renamed. *)
let () =
  let ident name = Ident.make Util.Loc.dummy name 0 in
  assert (not (Int.equal (Ident.hash (ident "a")) (Ident.hash (ident "b"))));
  assert (
    Int.equal (Ident.hash (Ident.with_name (ident "a") "b")) (Ident.hash (ident "b")));
  assert (Ident.equal (Ident.with_name (ident "a") "b") (ident "b"))
