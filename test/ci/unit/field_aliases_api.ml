open Base
open Raven
module R = Raven_api

let loc = R.Loc.none
let id value = R.Ident.make ~loc value
let name ?path value = R.Name.make ~loc ?path value
let variable value = R.Expr.var ~loc (name value)
let integer value = R.Expr.int ~loc value
let field ?path value = R.Expr.field ~loc (variable "x") (name ?path value)
let own expression = R.Expr.own ~loc [ expression; variable "n"; R.Expr.real ~loc 1.0 ]
let spec expression = R.Spec.make expression

let read member constrained =
  let result = R.Expr.binary ~loc Eq (variable "r") (variable "n") in
  let result =
    if constrained then
      R.Expr.binary ~loc And result (R.Expr.binary ~loc Geq (variable "r") (integer 0))
    else result
  in
  R.Member.callable
    (R.Callable.proc ~loc
       ~formals:
         [
           R.Var.make ~loc (id "x") (R.Type.ref ~loc);
           R.Var.make ~loc ~ghost:true (id "n") (R.Type.int ~loc);
         ]
       ~returns:[ R.Var.make ~loc (id "r") (R.Type.int ~loc) ]
       ~requires:[ spec (own (field member)) ]
       ~ensures:[ spec (own (field ~path:[ "Actual" ] member)); spec result ]
       (id ("read_" ^ member))
       (Some [ R.Stmt.assign ~loc [ variable "r" ] (R.Stmt.expr_rhs (field member)) ]))

let members =
  [
    R.Member.callable
      (R.Callable.func ~loc
         ~formals:[ R.Var.make ~loc (id "value") (R.Type.int ~loc) ]
         ~returns:[ R.Var.make ~loc (id "result") (R.Type.bool ~loc) ]
         (id "nonnegative")
         (Some (R.Expr.binary ~loc Geq (variable "value") (integer 0))));
    R.Member.module_ ~loc (id "Actual")
      [
        R.Member.field ~loc (id "plain") (R.Type.int ~loc);
        R.Member.field ~loc ~where:(name "nonnegative") (id "checked") (R.Type.int ~loc);
      ];
    R.Member.field_alias ~loc (id "plain") (name ~path:[ "Actual" ] "plain");
    R.Member.field_alias ~loc (id "checked") (name ~path:[ "Actual" ] "checked");
    read "plain" false;
    read "checked" true;
  ]

let program = R.Program.make ~loc members

let check_emission () =
  let source = R.Program.to_string program in
  let lexbuf = Lexing.from_string source in
  Frontend.Lexer.set_file_name lexbuf "field_aliases_api.rav";
  let _, parsed =
    Driver.parse_cu ~diagnostics:(Util.Diagnostics.create ())
      ~includes:(Driver.create_includes ()) "." Ast.Predefs.prog_ident lexbuf
  in
  let aliases =
    List.filter_map parsed.mod_def ~f:(function
      | Ast.Module.SymbolDef (FieldDef { field_alias = Some target; _ }) ->
          Some (Ast.QualIdent.to_string target)
      | _ -> None)
  in
  assert (List.equal String.equal aliases [ "Actual.plain"; "Actual.checked" ])

let verify expected program =
  let result = R.verify program in
  if expected then
    begin if not result.verified then
      failwith
        (String.concat ~sep:"\n" (List.map result.diagnostics ~f:R.Diagnostic.to_string))
    end
  else begin
    assert (not result.verified);
    assert (
      List.exists result.diagnostics ~f:(fun diagnostic ->
          match diagnostic.R.Diagnostic.kind with Verification -> true | _ -> false))
  end

let () =
  check_emission ();
  verify true program;
  let invalid =
    R.Member.callable
      (R.Callable.proc ~loc (id "invalid")
         (Some
            (R.Stmt.local ~loc
               ~init:(R.Stmt.new_rhs [ (name "checked", Some (integer (-1))) ])
               (id "x"))))
  in
  verify false (R.Program.make ~loc (members @ [ invalid ]))
