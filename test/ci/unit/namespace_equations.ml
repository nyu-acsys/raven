open Base
open Raven
open Ast
module Equations = Frontend.NamespaceEquations

let loc = Util.Loc.dummy
let id name = Ident.make loc name 0
let qi name = QualIdent.from_ident (id name)
let formal name = Type.mk_var_decl ~loc (id name) Type.int
let use name = Expr.from_var_decl (formal name)
let own name args = Callable.invariant_mask_entry (qi name) args
let dependencies name args = (Callable.MaskHead.Dependencies (qi name), args)

let declaration ?(formals = []) name definition : NamespaceContract.namespace_decl =
  { name = qi name; formals; definition }

let expect actual expected =
  assert (Callable.mask_equal actual (Callable.mask_canon expected))

let expand equations name args =
  Equations.expand_required equations [ dependencies name args ]

let test_abstract_and_empty () =
  let equations =
    Equations.solve
      [
        declaration ~formals:[ formal "x" ] "Opaque" Abstract;
        declaration "Empty" (Defined []);
      ]
  in
  expect
    (expand equations "Opaque" [ Expr.mk_int 3 ])
    [ dependencies "Opaque" [ Expr.mk_int 3 ] ];
  expect (expand equations "Empty" []) [];
  expect
    (expand equations "External" [ use "arg" ])
    [ dependencies "External" [ use "arg" ] ];
  assert (Option.is_none (Equations.upper_bound equations (qi "External")))

let test_dependency_substitution () =
  let equations =
    Equations.solve
      [
        declaration
          ~formals:[ formal "x" ]
          "Outer"
          (Defined [ dependencies "Inner" [ use "x" ] ]);
        declaration
          ~formals:[ formal "y" ]
          "Inner"
          (Defined [ own "I" [ use "y" ]; dependencies "Opaque" [ use "y" ] ]);
        declaration ~formals:[ formal "z" ] "Opaque" Abstract;
      ]
  in
  expect
    (expand equations "Outer" [ Expr.mk_int 7 ])
    [ own "I" [ Expr.mk_int 7 ]; dependencies "Opaque" [ Expr.mk_int 7 ] ];
  expect
    (Equations.expand_required equations [ own "Outer" [ Expr.mk_int 7 ] ])
    [ own "Outer" [ Expr.mk_int 7 ] ]

let test_prefix_truncation () =
  let global = Expr.mk_var ~typ:Type.int (QualIdent.from_list [ id "Module"; id "g" ]) in
  let equations =
    Equations.solve
      [
        declaration
          ~formals:[ formal "x"; formal "y" ]
          "Partial"
          (Defined [ own "I" [ global; use "x"; use "y"; Expr.mk_int 9 ] ]);
        declaration
          ~formals:[ formal "x" ]
          "Hidden"
          (Defined [ own "I" [ use "x"; use "hidden"; Expr.mk_int 9 ] ]);
      ]
  in
  expect
    (expand equations "Partial" [ use "caller" ])
    [ own "I" [ global; use "caller" ] ];
  expect (expand equations "Partial" [ use "y" ]) [ own "I" [ global; use "y" ] ];
  expect (expand equations "Partial" []) [ own "I" [ global ] ];
  expect (expand equations "Hidden" [ use "caller" ]) [ own "I" [ use "caller" ] ]

let test_recursive_empty () =
  let equations =
    Equations.solve
      [
        declaration ~formals:[ formal "x" ] "P" (Defined [ dependencies "Q" [ use "x" ] ]);
        declaration ~formals:[ formal "y" ] "Q" (Defined [ dependencies "P" [ use "y" ] ]);
        declaration "Self" (Defined [ dependencies "Self" [] ]);
      ]
  in
  List.iter [ "P"; "Q"; "Self" ] ~f:(fun name -> expect (expand equations name []) [])

let test_recursive_widening () =
  let transformed = Expr.mk_app ~typ:Type.int (Var (qi "f")) [ use "x" ] in
  let original = [ own "I" [ use "x" ]; dependencies "P" [ transformed ] ] in
  let declarations =
    [
      declaration ~formals:[ formal "x" ] "P" (Defined original);
      declaration
        ~formals:[ formal "y" ]
        "Client"
        (Defined [ dependencies "P" [ use "y" ]; own "J" [ use "y" ] ]);
    ]
  in
  let equations = Equations.solve declarations in
  expect (expand equations "P" [ Expr.mk_int 1 ]) [ own "I" [] ];
  expect
    (expand equations "Client" [ Expr.mk_int 2 ])
    [ own "I" []; own "J" [ Expr.mk_int 2 ] ];
  begin match Equations.upper_bound equations (qi "P") with
  | Some bound -> expect bound [ own "I" [] ]
  | None -> assert false
  end;
  (* Widening a requirement never rewrites the equation used for granted masks. *)
  assert (Poly.equal (Equations.declarations equations) declarations);
  match (List.hd_exn (Equations.declarations equations)).definition with
  | Defined body -> expect body original
  | Abstract -> assert false

let test_recursive_opaque_leaf () =
  let equations =
    Equations.solve
      [
        declaration
          ~formals:[ formal "x" ]
          "P"
          (Defined [ dependencies "Q" [ use "x" ]; dependencies "External" [ use "x" ] ]);
        declaration
          ~formals:[ formal "y" ]
          "Q"
          (Defined [ dependencies "P" [ use "y" ]; own "I" [ use "y" ] ]);
      ]
  in
  List.iter [ "P"; "Q" ] ~f:(fun name ->
      expect
        (expand equations name [ Expr.mk_int 0 ])
        [ own "I" []; dependencies "External" [] ])

let () =
  test_abstract_and_empty ();
  test_dependency_substitution ();
  test_prefix_truncation ();
  test_recursive_empty ();
  test_recursive_widening ();
  test_recursive_opaque_leaf ()
