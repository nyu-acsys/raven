open Base
module R = Raven_api

let loc = R.Loc.none
let id = R.Ident.make ~loc
let name = R.Name.make ~loc
let x = R.Expr.var ~loc (name "x")
let formals = [ R.Var.make ~loc (id "x") (R.Type.int ~loc) ]
let call member = R.Expr.call ~loc (name member) [ x ]
let resource member = R.Spec.make (call member)

let invariant ?ancestry member body =
  R.Member.callable (R.Callable.func ~loc ~kind:Inv ~formals ?ancestry (id member) body)

let visit body =
  R.Member.callable
    (R.Callable.proc ~loc ~kind:Lemma ~formals
       ~requires:[ resource "root"; resource "leaf" ]
       ~ensures:[ resource "root"; resource "leaf" ]
       ~opens:(loc, [ (name "root", [ x ]) ])
       (id "visit") body)

let invariant_with_witness () =
  R.Member.callable
    (R.Callable.func ~loc ~kind:Inv ~formals
       ~returns:
         [ R.Var.make ~loc ~ghost:true ~implicit:true (id "value") (R.Type.int ~loc) ]
       (id "stored") None)

let program =
  R.Program.make ~loc
    [
      R.Member.free (invariant_with_witness ());
      R.Member.callable
        (R.Callable.proc ~loc ~kind:Lemma ~formals
           ~requires:[ R.Spec.make (R.Expr.call ~loc (name "stored") [ x; x ]) ]
           ~ensures:[ R.Spec.make (R.Expr.call ~loc (name "stored") [ x; x ]) ]
           ~opens:(loc, [ (name "stored", [ x ]) ])
           (id "preserve") (Some []));
      R.Member.module_ ~loc ~interface:true (id "Public")
        [
          invariant "root" None;
          invariant ~ancestry:(Within (name "root", [ x ])) "leaf" None;
          visit None;
        ];
      R.Member.module_ ~loc
        ~implements:[ (name "Public", []) ]
        (id "Actual")
        [
          invariant "root" (Some (call "leaf"));
          invariant
            ~ancestry:(Parent (name "root", [ x ]))
            "leaf"
            (Some (R.Expr.bool ~loc true));
          visit
            (Some
               [
                 R.Stmt.unfold ~loc (name "root") [ x ];
                 R.Stmt.unfold ~loc (name "leaf") [ x ];
                 R.Stmt.fold ~loc (name "leaf") [ x ];
                 R.Stmt.fold ~loc (name "root") [ x ];
               ]);
        ];
    ]

let () =
  let source = R.Program.to_string program in
  assert (String.is_substring source ~substring:"parent root(x)");
  assert (String.is_substring source ~substring:"within root(x)");
  let result = R.verify program in
  if not result.verified then
    failwith
      (String.concat ~sep:"\n" (List.map result.diagnostics ~f:R.Diagnostic.to_string))
