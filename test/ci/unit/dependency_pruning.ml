open Base
open Raven
open Ast
module Dependencies = Backend.Dependencies
module Graph = Dependencies.Graph

let parse ~machine_free text =
  let diagnostics = Util.Diagnostics.create () in
  let lexbuf = Lexing.from_string text in
  Frontend.Lexer.set_file_name lexbuf "dependency_pruning.rav";
  let _, parsed =
    Driver.parse_cu ~diagnostics ~includes:(Driver.create_includes ()) "."
      Predefs.prog_ident lexbuf
  in
  let parsed =
    if not machine_free then parsed
    else
      {
        parsed with
        Module.mod_def =
          List.map parsed.mod_def ~f:(function
            | Module.SymbolDef (ModDef imported) ->
                Module.SymbolDef (ModDef (Module.set_machine_free imported))
            | instruction -> instruction);
      }
  in
  let tbl =
    SymbolTbl.add_symbol ~diagnostics (Module.ModDef parsed) (SymbolTbl.create ())
  in
  Frontend.Typing.check_module ~tbl ~diagnostics parsed

let schedule ?(machine_free = false) text =
  let tbl, typed = parse ~machine_free text in
  let placements, _, _, _ = Dependencies.analyze tbl [ typed ] Graph.empty Graph.empty in
  List.concat_map placements ~f:snd
  |> List.map ~f:(fun name -> Ident.name (QualIdent.unqualify name))

let program =
  "func b() returns (r: Int) { 1 }\n\
   func c() returns (r: Int) { 2 }\n\
   proc check() { assert b() + c() == 3; }"

let () =
  let baseline = schedule program in
  assert (List.equal String.equal baseline [ "b"; "c"; "check" ]);
  let admitted = schedule (program ^ "\nfree func a() returns (r: Int) { c() }") in
  assert (List.equal String.equal baseline admitted);
  let imported =
    schedule ~machine_free:true
      (program ^ "\nmodule A { func a() returns (r: Int) { c() } }")
  in
  assert (List.equal String.equal baseline imported);
  let automatic = schedule (program ^ "\nfree auto lemma law() ensures b() == 1") in
  assert (List.mem automatic "law" ~equal:String.equal)

let () =
  let id = Ident.make Util.Loc.dummy "target" 0 |> QualIdent.from_ident in
  let source = Ident.make Util.Loc.dummy "source" 0 |> QualIdent.from_ident in
  let graph = Graph.add_edge Graph.empty source id in
  let kept = Set.singleton (module QualIdent) id in
  let restricted = Graph.restrict graph kept in
  assert (Set.equal kept (Graph.vertices restricted));
  assert (List.equal (List.equal QualIdent.equal) (Graph.topsort restricted) [ [ id ] ])
