open Base
open Raven
open Ast
module Entailment = Frontend.NamespaceEntailment

let id name = Ident.make Util.Loc.dummy name 0

let parse source =
  let diagnostics = Util.Diagnostics.create () in
  let lexbuf = Lexing.from_string source in
  Frontend.Lexer.set_file_name lexbuf "namespace_witnesses.rav";
  let _, parsed =
    Driver.parse_cu ~diagnostics ~includes:(Driver.create_includes ()) "."
      Predefs.prog_ident lexbuf
  in
  let table =
    SymbolTbl.add_symbol ~diagnostics (Module.ModDef parsed) (SymbolTbl.create ())
  in
  Frontend.Typing.check_module ~tbl:table ~diagnostics parsed

let test_generated_instance_identity () =
  let source =
    "interface Element { rep type T }\n\
     module Base[E: Element] { rep type T = Int inv region(x: Int) { true } }\n\
     interface View { module E: Element module A = Base[E] }\n\
     module Make[E: Element]: View {}"
  in
  let table, typed = parse source in
  let make =
    List.find_map typed.mod_def ~f:(function
      | Module.SymbolDef (ModDef module_)
        when String.equal (Ident.name module_.mod_decl.mod_decl_name) "Make" ->
          Some module_
      | Module.SymbolDef _ | Module.Import _ -> None)
    |> Option.value_exn
  in
  let is_invariant name =
    match
      SymbolTbl.resolve_and_find ~implementation:true ~read_only:true name
        (SymbolTbl.goto name table)
    with
    | Some (_, _, Module.CallDef call, _) ->
        Poly.(call.call_decl.call_decl_kind = Callable.Invariant)
    | Some (_, _, _, _) | None -> false
  in
  let instances =
    List.filter_map make.mod_decl.mod_decl_instance_subst ~f:(fun (source, target) ->
        let source = QualIdent.append source (id "region") in
        let target = QualIdent.append (QualIdent.from_list target) (id "region") in
        if (not (QualIdent.equal source target)) && is_invariant target then
          Some (source, target)
        else None)
  in
  assert (not (List.is_empty instances));
  List.iter instances ~f:(fun (source, target) ->
      let check =
        let open Rewriter.Syntax in
        let* actual = Entailment.canonical_name source in
        let* expected = Entailment.canonical_name target in
        let* state = Entailment.create [] in
        let+ separate =
          Entailment.entails state ~assumptions:[]
            {
              NamespaceContract.left = [ Callable.invariant_mask_entry source [] ];
              right = [ Callable.invariant_mask_entry target [] ];
              loc = Util.Loc.dummy;
            }
        in
        (actual, expected, separate)
      in
      let _, (actual, expected, separate) = Rewriter.eval check table in
      assert (QualIdent.equal actual expected);
      assert (not separate))

let test_fixed_constructor_identity () =
  let table, _ =
    parse
      "interface E {}\n\
       module Maker[P: E] { inv made(x: Int) { true } }\n\
       module Client[P: E] {\n\
       inv local(x: Int) { true }\n\
       module F = Maker[P] }"
  in
  let qi names = QualIdent.from_list (Predefs.prog_ident :: List.map names ~f:id) in
  let own name = [ Callable.invariant_mask_entry (qi name) [] ] in
  let condition : NamespaceContract.separation_requirement =
    {
      left = own [ "Client"; "F"; "made" ];
      right = own [ "Client"; "local" ];
      loc = Util.Loc.dummy;
    }
  in
  let query =
    let open Rewriter.Syntax in
    let* state = Entailment.create [] in
    Entailment.entails state ~assumptions:[] condition
  in
  assert (snd (Rewriter.eval query table))

let () =
  test_generated_instance_identity ();
  test_fixed_constructor_identity ()
