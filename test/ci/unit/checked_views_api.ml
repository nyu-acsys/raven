open Base
open Raven
module R = Raven_api

let loc = R.Loc.none
let id value = R.Ident.make ~loc value
let name value = R.Name.make ~loc value
let variable value = R.Expr.var ~loc (name value)
let integer value = R.Expr.int ~loc value
let spec expression = R.Spec.make expression

let program ?(sealed = false) value =
  let returns = [ R.Var.make ~loc (id "r") (R.Type.int ~loc) ] in
  let requirement =
    R.Callable.proc ~loc ~returns
      ~ensures:[ spec (R.Expr.binary ~loc Gt (variable "r") (integer 0)) ]
      (id "operation") None
  in
  let actual =
    R.Callable.proc ~loc ~returns
      ~ensures:[ spec (R.Expr.binary ~loc Eq (variable "r") (integer value)) ]
      (id "operation")
      (Some [ R.Stmt.assign ~loc [ variable "r" ] (R.Stmt.expr_rhs (integer value)) ])
  in
  R.Program.make ~loc
    [
      R.Member.module_ ~loc ~interface:true (id "Required")
        [ R.Member.callable requirement ];
      R.Member.module_ ~loc (id "Actual") [ R.Member.callable actual ];
      R.Member.checked_view ~loc ~typ:(name "Required") ~sealed (id "View")
        (name "Actual");
    ]

let emission sealed =
  let source = R.Program.to_string (program ~sealed 1) in
  let lexbuf = Lexing.from_string source in
  Frontend.Lexer.set_file_name lexbuf "checked_views_api.rav";
  let _, parsed =
    Driver.parse_cu ~diagnostics:(Util.Diagnostics.create ())
      ~includes:(Driver.create_includes ()) "." Ast.Predefs.prog_ident lexbuf
  in
  match List.last parsed.mod_def with
  | Some (Ast.Module.SymbolDef (ModInst view)) ->
      assert view.mod_inst_is_checked;
      assert (Bool.equal view.mod_inst_is_sealed sealed)
  | _ -> failwith "checked view API did not preserve its binding"

let verify valid value =
  let result = R.verify value in
  if valid then
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
  emission false;
  emission true;
  verify true (program 1);
  verify false (program 0);
  verify true (program ~sealed:true 1);
  verify true (program 1)
