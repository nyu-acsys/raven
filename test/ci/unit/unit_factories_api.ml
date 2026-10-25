open Base
open Raven
module R = Raven_api

let loc = R.Loc.none
let id name = R.Ident.make ~loc name
let name ?path value = R.Name.make ~loc ?path value
let typ owner = R.Type.named ~loc (name ~path:[ owner ] "T") []
let variable value = R.Expr.var ~loc (name value)

let program ~fresh_result =
  let token =
    R.Type.data ~loc
      [ R.Type.variant ~loc (id "token") [ (id "value", R.Type.int ~loc) ] ]
  in
  let result_owner = if fresh_result then "Second" else "Copy" in
  let copy =
    R.Callable.proc ~loc
      ~formals:[ R.Var.make ~loc (id "value") (typ "First") ]
      ~returns:[ R.Var.make ~loc (id "result") (typ result_owner) ]
      (id "copy")
      (Some
         [ R.Stmt.assign ~loc [ variable "result" ] (R.Stmt.expr_rhs (variable "value")) ])
  in
  R.Program.make ~loc
    [
      R.Member.unit_factory ~loc (id "Fresh")
        [ R.Member.type_ ~loc (id "T") (Some token) ];
      R.Member.alias ~loc (id "FactoryAlias") (name "Fresh");
      R.Member.unit_instance ~loc (id "First") (name "FactoryAlias");
      R.Member.unit_instance ~loc (id "Second") (name "Fresh");
      R.Member.alias ~loc (id "Copy") (name "First");
      R.Member.callable copy;
    ]

let parse source =
  let lexbuf = Lexing.from_string source in
  Frontend.Lexer.set_file_name lexbuf "unit_factories_api.rav";
  let _, program =
    Driver.parse_cu ~diagnostics:(Util.Diagnostics.create ())
      ~includes:(Driver.create_includes ()) "." Ast.Predefs.prog_ident lexbuf
  in
  program

let check_emission program =
  let source = R.Program.to_string program in
  let parsed = parse source in
  begin match parsed.mod_def with
  | [
   Ast.Module.SymbolDef (ModDef factory);
   SymbolDef (ModInst factory_alias);
   SymbolDef (ModInst first);
   SymbolDef (ModInst second);
   SymbolDef (ModInst copy);
   SymbolDef (CallDef _);
  ] ->
      begin match factory.mod_decl.mod_decl_parameters with
      | Ast.Module.UnitParameter -> ()
      | Structure | NamedParameters _ -> assert false
      end;
      List.iter [ factory_alias; copy ] ~f:(fun alias ->
          match alias.Ast.Module.mod_inst_def with
          | Some (Alias _) -> ()
          | None | Some (Apply _ | ApplyUnit _) -> assert false);
      List.iter [ first; second ] ~f:(fun instance ->
          match instance.Ast.Module.mod_inst_def with
          | Some (ApplyUnit _) -> ()
          | None | Some (Alias _ | Apply _) -> assert false)
  | _ -> failwith "unit factory API emission changed module structure"
  end;
  let diagnostics = Util.Diagnostics.create () in
  let config : Driver.config =
    {
      no_library = true;
      typecheck_only = true;
      lsp_mode = false;
      lsp_annotations = false;
      base_dir = "";
      prog_stats = false;
      smt_timeout = R.default_options.smt_timeout;
      smt_diagnostics = false;
      max_errors = None;
      log_level = None;
      strict = false;
      only = None;
      counterexamples = false;
      fingerprints = false;
      cache_dir = None;
    }
  in
  Driver.check_program ~includes:(Driver.create_includes ())
    ~extension_mode:(`Explicit Ext.ProphecyExt) ~diagnostics config parsed;
  assert (not (Util.Diagnostics.has_errors diagnostics))

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
  let shared = program ~fresh_result:false in
  check_emission shared;
  verify true shared;
  verify false (program ~fresh_result:true);
  verify true (program ~fresh_result:false)
