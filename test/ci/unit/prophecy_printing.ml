open Base
open Raven

let printers =
  let (module Extension) = Ext.module_map Ext.ProphecyExt in
  Ast.Rewriter.printers_of_ext_hooks (Ext.to_ext_hooks (module Extension : ExtApi.Ext))

let prophecy one_shot =
  Ast.Type.mk_app (TypeExt (Ext.ProphecyExtInstance.ProphId one_shot)) [ Ast.Type.bool ]

let print typ = Stdlib.Format.asprintf "%a" printers.pr_type typ

let parse printed =
  let diagnostics = Util.Diagnostics.create () in
  let includes = Driver.create_includes () in
  let source = Lexing.from_string ("ghost field prophecy: " ^ printed) in
  Frontend.Lexer.set_file_name source "prophecy_printing.rav";
  snd
    (Driver.parse_cu ~diagnostics ~includes (Stdlib.Sys.getcwd ()) Ast.Predefs.prog_ident
       source)

let roundtrip typ expected =
  let printed = print typ in
  assert (String.equal printed expected);
  let parsed = parse printed in
  let source = Stdlib.Format.asprintf "%a" printers.pr_module_instrs parsed.mod_def in
  assert (String.is_substring source ~substring:expected)

let () =
  roundtrip (prophecy false) "Proph[Bool]";
  roundtrip (prophecy true) "Proph[Bool, 1]";
  roundtrip
    (Ast.Type.mk_app Prod [ prophecy true; prophecy false ])
    "(Proph[Bool, 1], Proph[Bool])"
