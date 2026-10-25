open Base
module R = Raven_api

let line n =
  let position =
    {
      Lexing.pos_fname = "applicative_lifecycle.rav";
      pos_lnum = n;
      pos_bol = 0;
      pos_cnum = 0;
    }
  in
  R.Loc.make position position

let id ?(loc = R.Loc.none) value = R.Ident.make ~loc value
let name ?(loc = R.Loc.none) ?path value = R.Name.make ~loc ?path value
let typ owner = R.Type.named ~loc:R.Loc.none (name ~path:[ owner ] "T") []
let variable value = R.Expr.var ~loc:R.Loc.none (name value)

let program ~payload_type ~payload ~bad_application =
  let loc = line 1 in
  let data =
    R.Type.data ~loc [ R.Type.variant ~loc (id "wrap") [ (id "value", payload_type) ] ]
  in
  let family =
    R.Member.module_ ~loc
      ~params:[ (id "Element", name ~path:[ "Library" ] "Type") ]
      ~implements:[ (name ~path:[ "Library" ] "Type", []) ]
      (id "Family")
      [ R.Member.type_ ~loc ~rep:true (id "T") (Some data) ]
  in
  let ordinary at binding =
    let loc = line at in
    R.Member.instance ~loc
      ~def:(name ~loc "Family", [ R.Type.int ~loc ])
      (id ~loc binding) (name ~loc "Family")
  in
  let copy =
    R.Callable.proc ~loc:(line 50)
      ~formals:[ R.Var.make ~loc (id "value") (typ "First") ]
      ~returns:[ R.Var.make ~loc (id "result") (typ "Second") ]
      (id "copy")
      (Some
         [ R.Stmt.assign ~loc [ variable "result" ] (R.Stmt.expr_rhs (variable "value")) ])
  in
  let make =
    R.Callable.func ~loc:(line 60)
      ~returns:[ R.Var.make ~loc (id "result") (typ "First") ]
      (id "make")
      (Some (R.Expr.call ~loc (name ~path:[ "Second" ] "wrap") [ payload ]))
  in
  let members =
    [
      family;
      R.Member.module_ ~loc:(line 10) ~interface:true (id "Wrong")
        [ R.Member.field ~loc (id "required") (R.Type.int ~loc) ];
    ]
  in
  let members =
    if bad_application then
      let loc = line 30 in
      members
      @ [
          R.Member.instance ~loc
            ~def:(name ~loc "Family", [ R.Type.int ~loc ])
            (id ~loc "Broken") (name ~loc "Wrong");
        ]
    else members
  in
  R.Program.make ~loc
    (members
    @ [
        ordinary 40 "First";
        ordinary 41 "Second";
        R.Member.callable copy;
        R.Member.callable make;
      ])

let error_diagnostics (result : R.result) =
  List.filter result.diagnostics ~f:(fun diagnostic ->
      match diagnostic.R.Diagnostic.severity with Error -> true | Warning -> false)

let expect_success program =
  let result = R.verify program in
  if not result.verified then
    failwith
      (String.concat ~sep:"\n" (List.map result.diagnostics ~f:R.Diagnostic.to_string));
  assert (List.is_empty (error_diagnostics result))

let () =
  let loc = R.Loc.none in
  let integer ~bad_application =
    program ~payload_type:(R.Type.int ~loc) ~payload:(R.Expr.int ~loc 3) ~bad_application
  in
  let reusable = integer ~bad_application:false in
  expect_success reusable;
  expect_success reusable;
  let failed = R.verify (integer ~bad_application:true) in
  assert (not failed.verified);
  begin match error_diagnostics failed with
  | [ diagnostic ] ->
      begin match diagnostic.kind with
      | Type -> ()
      | Syntax | Verification | Unsupported | Internal | Other -> assert false
      end;
      assert ((R.Loc.start diagnostic.loc).pos_lnum = 30)
  | diagnostics ->
      failwith (String.concat ~sep:"\n" (List.map diagnostics ~f:R.Diagnostic.to_string))
  end;
  expect_success reusable;
  expect_success
    (program ~payload_type:(R.Type.bool ~loc) ~payload:(R.Expr.bool ~loc true)
       ~bad_application:false);
  expect_success reusable
