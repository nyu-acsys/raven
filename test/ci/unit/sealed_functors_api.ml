open Base
open Raven
module R = Raven_api

let loc = R.Loc.none
let id text = R.Ident.make ~loc text
let name text = R.Name.make ~loc text
let typ owner = R.Type.named ~loc (R.Name.make ~loc ~path:[ owner ] "T") []

let program ~unit ~different =
  let source =
    if unit then R.Member.unit_factory ~loc
    else
      R.Member.module_ ~loc
        ~params:[ (id "E", R.Name.make ~loc ~path:[ "Library" ] "Type") ]
  in
  let instantiate text =
    if unit then R.Member.unit_instance ~loc (id text) (name "Hidden")
    else
      R.Member.instance ~loc
        ~def:(name "Hidden", [ R.Type.int ~loc ])
        (id text) (name "Hidden")
  in
  let target =
    if different then if unit then typ "Second" else R.Type.int ~loc else typ "Copy"
  in
  let copy =
    R.Callable.proc ~loc
      ~formals:[ R.Var.make ~loc (id "value") (typ "First") ]
      ~returns:[ R.Var.make ~loc (id "result") target ]
      (id "copy")
      (Some
         [
           R.Stmt.assign ~loc
             [ R.Expr.var ~loc (name "result") ]
             (R.Stmt.expr_rhs (R.Expr.var ~loc (name "value")));
         ])
  in
  R.Program.make ~loc
    [
      R.Member.module_ ~loc ~interface:true (id "Signature")
        [ R.Member.type_ ~loc (id "T") None ];
      source
        ~implements:[ (name "Signature", []) ]
        (id "Implementation")
        [ R.Member.type_ ~loc (id "T") (Some (R.Type.int ~loc)) ];
      R.Member.alias ~loc ~typ:(name "Signature") ~sealed:true (id "Hidden")
        (name "Implementation");
      instantiate "First";
      instantiate "Second";
      R.Member.alias ~loc (id "Copy") (name "First");
      R.Member.callable copy;
    ]

let check_emission program =
  let lexbuf = Lexing.from_string (R.Program.to_string program) in
  Frontend.Lexer.set_file_name lexbuf "sealed_functors_api.rav";
  let _, parsed =
    Driver.parse_cu ~diagnostics:(Util.Diagnostics.create ())
      ~includes:(Driver.create_includes ()) "." Ast.Predefs.prog_ident lexbuf
  in
  match List.nth_exn parsed.mod_def 2 with
  | Ast.Module.SymbolDef (ModInst binding) -> assert binding.mod_inst_is_sealed
  | _ -> failwith "sealed alias API changed its binding"

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
          match diagnostic.R.Diagnostic.kind with Type -> true | _ -> false))
  end

let () =
  List.iter [ false; true ] ~f:(fun unit ->
      let shared = program ~unit ~different:false in
      check_emission shared;
      verify true shared;
      verify false (program ~unit ~different:true));
  verify true (program ~unit:false ~different:false)
