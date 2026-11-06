(* A printed [return] keeps its values on its line: the lexer takes a [return] ending a line
   to have none. *)

open Base
open Raven
open Ast

let () =
  let value =
    Expr.mk_var ~typ:Type.int
      (QualIdent.from_list [ Ident.make Util.Loc.dummy (String.make 120 'x') 0 ])
  in
  let return = Stmt.mk_return ~loc:Util.Loc.dummy (Expr.mk_tuple [ value; value ]) in
  let printed = Stdlib.Format.asprintf "%a" Stmt.pr return in
  assert (String.is_prefix printed ~prefix:"return (")
