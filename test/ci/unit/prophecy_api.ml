open Base
module R = Raven_api

let loc = R.Loc.none
let id value = R.Ident.make ~loc value
let variable value = R.Expr.var ~loc (R.Name.make ~loc value)
let payload = R.Type.bool ~loc
let predicted = variable "predicted"
let prophecy = variable "prophecy"
let actual = variable "actual"
let agreement = R.Expr.binary ~loc Eq predicted actual
let assertion expression = R.Stmt.assert_ ~loc (R.Spec.make expression)

let program body =
  let declarations =
    R.Stmt.local ~loc ~ghost:true ~typ:(R.Prophecy.type_ ~loc payload) (id "prophecy")
    @ R.Stmt.local ~loc ~ghost:true ~typ:payload (id "predicted")
  in
  R.Program.make ~loc
    [
      R.Member.callable
        (R.Callable.proc ~loc ~kind:Lemma
           ~formals:[ R.Var.make ~loc (id "actual") payload ]
           (id "predict")
           (Some
              [
                R.Stmt.ghost_block ~loc
                  (declarations
                  @ [
                      R.Prophecy.create ~loc payload prophecy predicted;
                      assertion (R.Prophecy.owns ~loc prophecy predicted);
                    ]
                  @ body);
              ]));
    ]

let check expected body =
  let result = R.verify (program body) in
  if not (Bool.equal result.verified expected) then
    failwith
      (String.concat ~sep:"\n" (List.map result.diagnostics ~f:R.Diagnostic.to_string));
  if not expected then
    assert (
      List.exists result.diagnostics ~f:(fun diagnostic ->
          Poly.equal diagnostic.R.Diagnostic.kind Verification
          && not (String.is_substring diagnostic.message ~substring:"timeout")))

let () =
  check true [ R.Prophecy.resolve ~loc prophecy actual; assertion agreement ];
  check false [ assertion agreement ];
  check false
    [ R.Prophecy.resolve ~loc prophecy actual; R.Prophecy.resolve ~loc prophecy actual ]
