open Base
open Raven
open Ast
module Inference = Frontend.NamespaceInference
module Entailment = Frontend.NamespaceEntailment
module Realization = Frontend.NamespaceRealization

let id name = Ident.make Util.Loc.dummy name 0
let qi names = QualIdent.from_list (Predefs.prog_ident :: List.map names ~f:id)

let infer source =
  let diagnostics = Util.Diagnostics.create () in
  let lexbuf = Lexing.from_string source in
  Frontend.Lexer.set_file_name lexbuf "namespace_guarded_grants.rav";
  let _, parsed =
    Driver.parse_cu ~diagnostics ~includes:(Driver.create_includes ()) "."
      Predefs.prog_ident lexbuf
  in
  let tbl =
    SymbolTbl.add_symbol ~diagnostics (Module.ModDef parsed) (SymbolTbl.create ())
  in
  let tbl, typed = Frontend.Typing.check_module ~tbl ~diagnostics parsed in
  Rewriter.eval (Inference.infer typed) tbl

let resolved tbl draft names =
  let path = qi names in
  let _, summary =
    Rewriter.eval (Rewriter.in_scope_of path (Inference.find_callable draft path)) tbl
  in
  Option.value_exn summary

let own_cell x = Callable.invariant_mask_entry (qi [ "cell" ]) [ x ]

let contains mask entry =
  List.exists mask ~f:(fun candidate -> Callable.mask_equal [ candidate ] [ entry ])

let test_guarded_constructor_credit () =
  let tbl, draft =
    infer
      "inv cell(x: Int) { true }\n\
       interface Resource { pred p(x: Int) }\n\
       module Empty: Resource { pred p(x: Int) { true } }\n\
       module Hidden: Resource { pred p(x: Int) { cell(x) } }\n\
       module Factory[R: Resource] {\n\
       lemma create(ghost x: Int) requires R.p(x) ensures cell(x) {}\n\
       lemma fresh(ghost x: Int) ensures cell(x) {}\n\
       lemma relay(ghost x: Int) requires R.p(x) ensures R.p(x) {}\n\
       lemma omitted(ghost x: Int) requires R.p(x) ensures R.p(x) opens {} {}\n\
       }\n\
       module Safe = Factory[Empty]\n\
       module Risk = Factory[Hidden]"
  in
  let generic = resolved tbl draft [ "Factory"; "create" ] in
  let x = Expr.from_var_decl (List.hd_exn generic.formals) in
  assert (not (contains generic.grants (own_cell x)));
  assert (
    List.exists generic.guarded_grants ~f:(fun guarded ->
        contains guarded.grants (own_cell x) && not (List.is_empty guarded.conditions)));
  let covers provided =
    let comparison =
      let open Rewriter.Syntax in
      let* context = Entailment.create (Map.data draft.namespaces) in
      Realization.grants_cover context ~assumptions:[] provided generic
    in
    snd (Rewriter.eval comparison tbl)
  in
  assert (covers generic);
  assert (not (covers { generic with guarded_grants = [] }));
  let stronger =
    {
      generic with
      guarded_grants =
        List.map generic.guarded_grants ~f:(fun grant -> { grant with conditions = [] });
    }
  in
  assert (covers stronger);
  let fresh = resolved tbl draft [ "Factory"; "fresh" ] in
  let x = Expr.from_var_decl (List.hd_exn fresh.formals) in
  assert (contains fresh.grants (own_cell x));
  let relay = resolved tbl draft [ "Factory"; "relay" ] in
  assert (List.is_empty relay.grants);
  let safe = resolved tbl draft [ "Safe"; "create" ] in
  let x = Expr.from_var_decl (List.hd_exn safe.formals) in
  assert (contains safe.grants (own_cell x));
  let risk = resolved tbl draft [ "Risk"; "create" ] in
  let x = Expr.from_var_decl (List.hd_exn risk.formals) in
  assert (not (contains risk.grants (own_cell x)));
  let omitted = resolved tbl draft [ "Risk"; "omitted" ] in
  assert (List.is_empty omitted.grants)

let () =
  match test_guarded_constructor_credit () with
  | () -> ()
  | exception Util.Error.Msg errors ->
      failwith (String.concat ~sep:"\n" (List.map errors ~f:Util.Error.to_string))
