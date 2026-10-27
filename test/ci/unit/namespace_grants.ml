open Base
open Raven
open Ast

let verify source =
  let diagnostics = Util.Diagnostics.create () in
  let ext_hooks = Ext.to_ext_hooks (Ext.module_map Ext.DefaultExt) in
  let parse ~root ~free tbl source =
    let lexbuf = Lexing.from_string source in
    Frontend.Lexer.set_file_name lexbuf "namespace_grants.rav";
    let _, parsed =
      Driver.parse_cu ~diagnostics ~includes:(Driver.create_includes ()) "." root lexbuf
    in
    let parsed = if free then Module.set_unit_free parsed else parsed in
    let tbl = SymbolTbl.add_symbol ~diagnostics (Module.ModDef parsed) tbl in
    Frontend.Typing.check_module ~ext_hooks ~tbl ~diagnostics parsed
  in
  let library_source =
    String.concat ~sep:"\n" (List.map Library.library_sources ~f:snd)
  in
  let tbl, library =
    parse ~root:Predefs.lib_ident ~free:true (SymbolTbl.create ()) library_source
  in
  let tbl, lowering =
    parse ~root:Predefs.lowering_ident ~free:true tbl (snd Library.lowering_source)
  in
  let tbl, program = parse ~root:Predefs.prog_ident ~free:false tbl source in
  let tbl, elaborated =
    List.fold_map [ library; lowering; program ] ~init:tbl ~f:(fun tbl typed ->
        Frontend.Elaboration.elaborate_module ~ext_hooks ~tbl ~diagnostics typed)
  in
  let tbl, processed =
    List.fold_map elaborated ~init:tbl ~f:(fun tbl elaborated ->
        Driver.lower_cu ~ext_hooks ~diagnostics tbl elaborated None)
  in
  let module Solver = Backend.Smt.SmtSolver in
  let timeout = 10000 in
  let session = Solver.init ~logging:false timeout in
  Stdlib.Fun.protect
    ~finally:(fun () -> Solver.stop session)
    (fun () ->
      Backend.SmtPreamble.initialize session ~diagnostics:false ~timeout;
      Backend.SmtPreamble.declare_tuple_sorts session
        (Backend.Smt.TupleArities.of_symbols (Map.data tbl.tbl_symbols));
      let context = Backend.CheckerContext.create ~diagnostics session in
      ignore
        (Driver.backend_check_cu tbl context processed : Backend.CheckerContext.context));
  if Util.Diagnostics.has_errors diagnostics then
    failwith
      (String.concat ~sep:"\n"
         (List.map (Util.Diagnostics.report_errors diagnostics) ~f:Util.Error.to_string))

let test_counter () =
  verify
    "field value: Int\n\
     interface Counter {\n\
     pred valid(c: Ref, v: Int)\n\
     proc create() returns (c: Ref) ensures valid(c, 0)\n\
     proc increment(c: Ref, ghost v: Int)\n\
     requires valid(c, v) ensures valid(c, v + 1)\n\
     proc get(c: Ref, ghost v: Int) returns (r: Int)\n\
     requires valid(c, v) ensures valid(c, v) && r == v }\n\
     module Concrete: Counter {\n\
     pred valid(c: Ref, v: Int) { own(c.value, v) }\n\
     proc create() returns (c: Ref) { c := new (value: 0); fold valid(c, 0); }\n\
     proc increment(c: Ref, ghost v: Int) {\n\
     unfold valid(c, v); var n := c.value; c.value := n + 1; fold valid(c, v + 1); }\n\
     proc get(c: Ref, ghost v: Int) returns (r: Int) {\n\
     unfold valid(c, v); r := c.value; fold valid(c, v); } }\n\
     module Client[C: Counter] { proc run() {\n\
     var c := C.create(); C.increment(c, 0);\n\
     var r := C.get(c, 1); assert r == 1; } }\n\
     module Applied = Client[Concrete]"

let () =
  match test_counter () with
  | () -> ()
  | exception Util.Error.Msg errors ->
      failwith (String.concat ~sep:"\n" (List.map errors ~f:Util.Error.to_string))
