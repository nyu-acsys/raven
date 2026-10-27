open Base
open Raven
open Ast
module Closure = Frontend.NamespaceClosure

let id name = Ident.make Util.Loc.dummy name 0
let qi names = QualIdent.from_list (Predefs.prog_ident :: List.map names ~f:id)

let parse source =
  let diagnostics = Util.Diagnostics.create () in
  let lexbuf = Lexing.from_string source in
  Frontend.Lexer.set_file_name lexbuf "namespace_origins.rav";
  let _, parsed =
    Driver.parse_cu ~diagnostics ~includes:(Driver.create_includes ()) "."
      Predefs.prog_ident lexbuf
  in
  let tbl =
    SymbolTbl.add_symbol ~diagnostics (Module.ModDef parsed) (SymbolTbl.create ())
  in
  Frontend.Typing.check_module ~tbl ~diagnostics parsed

let freeze source =
  let tbl, typed = parse source in
  let tbl, collected = Rewriter.eval (Closure.collect typed) tbl in
  let tbl, closed = Rewriter.eval (Closure.close collected) tbl in
  snd (Rewriter.eval (Closure.freeze closed collected.program) tbl)

let summary = function
  | NamespaceContract.Module summary -> summary
  | Functor functor_ ->
      begin match functor_.result with
      | Module summary -> summary
      | Functor _ -> assert false
      end

let root program =
  Option.value_exn program.Module.mod_decl.mod_decl_mask_contract |> summary

let child parent name =
  List.Assoc.find_exn parent.NamespaceContract.modules (id name) ~equal:Ident.equal
  |> summary

let methods parent name =
  List.filter_map parent.NamespaceContract.callables ~f:(fun (candidate, method_) ->
      if String.equal (Ident.name candidate) name then Some method_ else None)

let method_ parent name =
  match methods parent name with [ method_ ] -> method_ | _ -> assert false

let formal method_ = Expr.from_var_decl (List.hd_exn method_.NamespaceContract.formals)
let mask_is actual expected = assert (Callable.mask_equal actual expected)

let test_omitted_and_repeated_contracts () =
  let frozen =
    freeze
      "inv hidden(x: Int) { true }\n\
       interface Parent { pred p(x: Int)\n\
       lemma omitted(ghost x: Int) requires p(x)\n\
       lemma repeated(ghost x: Int) requires p(x) }\n\
       module Child: Parent { pred p(x: Int) { hidden(x) }\n\
       lemma omitted(ghost y: Int) {}\n\
       lemma repeated(ghost z: Int) requires p(z) {} }"
  in
  let root = root frozen in
  let parent = child root "Parent" in
  let implementation = child root "Child" in
  List.iter [ "omitted"; "repeated" ] ~f:(fun name ->
      mask_is (method_ parent name).requires [];
      mask_is (method_ implementation name).requires [])

let test_reordered_members_with_overloads () =
  let frozen =
    freeze
      "inv hidden(x: Int) { true }\n\
       interface Parent { pred p(x: Int) inv flag(x: Bool)\n\
       func choose(x: Int) returns (r: Int)\n\
       func choose(x: Bool) returns (r: Bool)\n\
       lemma opaque_use(ghost x: Int) requires p(x)\n\
       lemma visible_use(ghost x: Bool) requires flag(x) }\n\
       module Child: Parent { pred p(x: Int) { hidden(x) }\n\
       inv flag(x: Bool) { true }\n\
       func choose(x: Bool) returns (r: Bool) { x }\n\
       func choose(x: Int) returns (r: Int) { x }\n\
       lemma visible_use(ghost b: Bool) requires flag(b) {}\n\
       lemma opaque_use(ghost n: Int) requires p(n) {} }"
  in
  let implementation = child (root frozen) "Child" in
  let opaque = method_ implementation "opaque_use" in
  let visible = method_ implementation "visible_use" in
  mask_is opaque.requires [];
  mask_is visible.requires
    [ Callable.invariant_mask_entry (qi [ "Child"; "flag" ]) [ formal visible ] ]

let test_applied_parent () =
  let frozen =
    freeze
      "interface Element { inv slot(x: Int) }\n\
       interface Parent[P: Element] {\n\
       lemma use(ghost x: Int) requires P.slot(x) }\n\
       module Child[Q: Element]: Parent[Q] {\n\
       lemma use(ghost y: Int) {} }"
  in
  let implementation = child (root frozen) "Child" in
  let use = method_ implementation "use" in
  mask_is use.requires
    [ Callable.invariant_mask_entry (qi [ "Child"; "Q"; "slot" ]) [ formal use ] ]

let test_unit_alias_parent () =
  let frozen =
    freeze
      "inv hidden(x: Int) { true }\n\
       interface Parent() { pred p(x: Int)\n\
       lemma use(ghost x: Int) requires p(x) }\n\
       interface ParentAlias = Parent\n\
       module Child(): ParentAlias { pred p(x: Int) { hidden(x) }\n\
       lemma use(ghost y: Int) {} }\n\
       module Alias = Child\n\
       module Inst = Alias()"
  in
  let root = root frozen in
  mask_is (method_ (child root "Child") "use").requires [];
  mask_is (method_ (child root "Inst") "use").requires []

let () =
  match
    test_omitted_and_repeated_contracts ();
    test_reordered_members_with_overloads ();
    test_applied_parent ();
    test_unit_alias_parent ()
  with
  | () -> ()
  | exception Util.Error.Msg errors ->
      failwith (String.concat ~sep:"\n" (List.map errors ~f:Util.Error.to_string))
