open Base
open Raven
open Ast
module Closure = Frontend.NamespaceClosure
module Realization = Frontend.NamespaceRealization

let id name = Ident.make Util.Loc.dummy name 0

let parse source =
  let diagnostics = Util.Diagnostics.create () in
  let lexbuf = Lexing.from_string source in
  Frontend.Lexer.set_file_name lexbuf "namespace_realization.rav";
  let _, parsed =
    Driver.parse_cu ~diagnostics ~includes:(Driver.create_includes ()) "."
      Predefs.prog_ident lexbuf
  in
  let tbl =
    SymbolTbl.add_symbol ~diagnostics (Module.ModDef parsed) (SymbolTbl.create ())
  in
  let tbl, typed = Frontend.Typing.check_module ~tbl ~diagnostics parsed in
  (diagnostics, tbl, typed)

let validate source =
  let _, tbl, typed = parse source in
  let tbl, collected = Rewriter.eval (Closure.collect typed) tbl in
  let tbl, draft = Rewriter.eval (Closure.close collected) tbl in
  let tbl, frozen = Rewriter.eval (Closure.freeze draft collected.program) tbl in
  snd (Rewriter.eval (Realization.validate ~draft frozen) tbl)

let accept source = ignore (validate source : Module.t)

let expect_namespace_error action =
  match action () with
  | _ -> failwith "Expected an invariant namespace realization error"
  | exception Util.Error.Msg errors ->
      assert (
        List.exists errors ~f:(fun (kind, _, message) ->
            match kind with
            | Util.Error.Type ->
                String.is_substring (String.lowercase message) ~substring:"namespace"
            | _ -> false))

let reject source = expect_namespace_error (fun () -> validate source)
let regions = "interface Regions { inv i(x: Int) inv j(x: Int) }\n"

let opening_functor =
  "module F[P: Regions] {\n\
   lemma use(ghost x: Int) requires P.i(x) && P.j(x) {\n\
   unfold P.i(x); unfold P.j(x); fold P.j(x); fold P.i(x); } }\n"

let test_fixed_namespaces () =
  accept
    "inv first(x: Int) { true } inv second(x: Int) { true }\n\
     lemma use(ghost x: Int) requires first(x) && second(x) {\n\
     unfold first(x); unfold second(x); fold second(x); fold first(x); }"

let test_aliases () =
  let actual right =
    regions ^ opening_functor
    ^ "inv left(x: Int) { true } inv right(x: Int) { true }\n\
       module Actual: Regions { inv i(x: Int) = left inv j(x: Int) = " ^ right
    ^ " }\nmodule Instance = F[Actual]"
  in
  accept (actual "right");
  reject (actual "left")

let test_unit_freshness () =
  accept
    "module Factory() { inv cell(x: Int) { true } }\n\
     module First = Factory() module Second = Factory()\n\
     lemma use(ghost x: Int) requires First.cell(x) && Second.cell(x) {\n\
     unfold First.cell(x); unfold Second.cell(x);\n\
     fold Second.cell(x); fold First.cell(x); }"

let test_opaque_dependencies () =
  reject
    "inv cell(x: Int) { true }\n\
     interface Predicate { pred p(x: Int) }\n\
     module Actual: Predicate { pred p(x: Int) { cell(x) } }\n\
     module Worker[P: Predicate] {\n\
     lemma helper(ghost x: Int) requires P.p(x) {}\n\
     lemma use(ghost x: Int) requires cell(x) && P.p(x) {\n\
     unfold cell(x); helper(x); fold cell(x); } }\n\
     module Instance = Worker[Actual]"

let test_unused_aliases () =
  accept
    (regions
   ^ "inv hidden(x: Int) { true }\n\
      module Actual: Regions { inv i(x: Int) = hidden inv j(x: Int) = hidden }\n\
      module Unused[P: Regions] {} module Instance = Unused[Actual]")

let test_views () =
  let source binding right =
    regions ^ opening_functor
    ^ "inv left(x: Int) { true } inv right(x: Int) { true }\n\
       module Implementation { inv i(x: Int) = left inv j(x: Int) = " ^ right
    ^ " }\nmodule Actual " ^ binding
    ^ " Regions = checked Implementation\nmodule Instance = F[Actual]"
  in
  List.iter [ ":"; ":>" ] ~f:(fun binding ->
      accept (source binding "right");
      reject (source binding "left"))

let test_inheritance () =
  let source right =
    regions ^ "interface Extended: Regions {}\n" ^ opening_functor
    ^ "inv left(x: Int) { true } inv right(x: Int) { true }\n\
       module Actual: Extended { inv i(x: Int) = left inv j(x: Int) = " ^ right
    ^ " }\nmodule Instance = F[Actual]"
  in
  accept (source "right");
  reject (source "left")

let test_residual_application () =
  let source right =
    regions ^ opening_functor
    ^ "module Wrapper[P: Regions] { module Inner = F[P] }\n\
       inv left(x: Int) { true } inv right(x: Int) { true }\n\
       module Actual: Regions { inv i(x: Int) = left inv j(x: Int) = " ^ right
    ^ " }\nmodule Instance = Wrapper[Actual]"
  in
  accept (source "right");
  reject (source "left")

let comparator source expected =
  let _, tbl, typed = parse source in
  let tbl, frozen = Rewriter.eval (Closure.elaborate typed) tbl in
  let root = Option.value_exn frozen.Module.mod_decl.mod_decl_mask_contract in
  let members =
    match root with
    | NamespaceContract.Module summary -> summary.modules
    | Functor _ -> assert false
  in
  let path name = QualIdent.from_list [ Predefs.prog_ident; id name ] in
  let compare name =
    let open Rewriter.Syntax in
    let action =
      let* namespaces, _ = Closure.imported_summaries () in
      Realization.compatible ~declarations:(Map.data namespaces)
        ~owner:(QualIdent.from_ident Predefs.prog_ident)
        ~loc:Util.Loc.dummy ~established:true Realization.empty_environment
        ~actual_path:(path name) ~expected_path:(path expected)
        (List.Assoc.find_exn members (id name) ~equal:Ident.equal)
        (List.Assoc.find_exn members (id expected) ~equal:Ident.equal)
    in
    ignore
      (Rewriter.eval
         (Rewriter.eval_with_user_state ~init:(Map.empty (module QualIdent)) action)
         tbl)
  in
  compare

let test_functor_requirements () =
  let source =
    regions ^ opening_functor
    ^ "interface FunSig[X: Regions] {\n\
       lemma use(ghost x: Int) requires X.i(x) && X.j(x) }\n\
       module Good[X: Regions] {\n\
       lemma use(ghost x: Int) requires X.i(x) && X.j(x) {} }"
  in
  let compare = comparator source "FunSig" in
  compare "Good";
  expect_namespace_error (fun () -> compare "F")

let test_higher_order_application () =
  accept
    (regions
   ^ "interface FunSig[P: Regions] {\n\
      lemma use(ghost x: Int) requires P.i(x) && P.j(x) {\n\
      unfold P.i(x); unfold P.j(x); fold P.j(x); fold P.i(x); } }\n\
      module Good[P: Regions]: FunSig[P] {}\n\
      module Actual: Regions { inv i(x: Int) { true } inv j(x: Int) { true } }\n\
      module Higher[G: FunSig] { module Inside = G[Actual] }\n\
      module Instance = Higher[Good]")

let test_callable_mask_variance () =
  let source =
    "interface Wanted { inv i(x: Int) inv j(x: Int)\n\
     lemma use(ghost n: Int) requires i(n) ensures i(n) }\n\
     module Good { inv i(x: Int) { true } inv j(x: Int) { true }\n\
     lemma use(ghost value: Int) requires i(value) ensures i(value) {} }\n\
     module Stronger { inv i(x: Int) { true } inv j(x: Int) { true }\n\
     lemma use(ghost value: Int) requires i(value) && j(value) ensures i(value) {} }\n\
     module Weaker { inv i(x: Int) { true } inv j(x: Int) { true }\n\
     lemma use(ghost value: Int) requires i(value) {} }"
  in
  let compare = comparator source "Wanted" in
  compare "Good";
  expect_namespace_error (fun () -> compare "Stronger");
  expect_namespace_error (fun () -> compare "Weaker")

let test_sealed_constructor_outputs () =
  let source unit collapsed =
    let signature, constructor, application =
      if unit then
        ( "interface FactoryRegions(): Regions {}\n",
          "module Factory(): FactoryRegions {\n",
          "Hidden()" )
      else
        ( "interface Argument {} module Arg: Argument {}\n\
           interface FactoryRegions[P: Argument]: Regions {}\n",
          "module Factory[P: Argument]: FactoryRegions[P] {\n",
          "Hidden[Arg]" )
    in
    regions ^ opening_functor ^ signature ^ constructor
    ^ "inv first(x: Int) { true } inv second(x: Int) { true }\n\
       inv i(x: Int) = first inv j(x: Int) = "
    ^ (if collapsed then "first" else "second")
    ^ " }\nmodule Hidden :> FactoryRegions = Factory\nmodule Actual = " ^ application
    ^ "\nmodule Instance = F[Actual]"
  in
  List.iter [ false; true ] ~f:(fun unit ->
      accept (source unit false);
      reject (source unit true))

let test_concrete_module_formal () =
  let source actual =
    "module Base { inv cell(x: Int) { true }\n\
     lemma touch(ghost x: Int) requires cell(x) {} }\n\
     module Actual: Base {} module Other: Base {}\n\
     module W[P: Base] {\n\
     lemma use(ghost x: Int) requires Actual.cell(x) && P.cell(x) {\n\
     unfold Actual.cell(x); P.touch(x); fold Actual.cell(x); } }\n\
     module Applied = W[" ^ actual ^ "]"
  in
  accept (source "Other");
  reject (source "Actual")

let test_concrete_functor_formal () =
  reject
    "interface E {} module Arg: E {}\n\
     module Maker[P: E] { inv cell(x: Int) { true } }\n\
     module Fixed = Maker[Arg]\n\
     module W[G: Maker] { module Out = G[Arg]\n\
     lemma use(ghost x: Int) requires Fixed.cell(x) && Out.cell(x) {\n\
     unfold Fixed.cell(x); unfold Out.cell(x);\n\
     fold Out.cell(x); fold Fixed.cell(x); } }\n\
     module Applied = W[Maker]"

let () =
  match
    test_fixed_namespaces ();
    test_aliases ();
    test_unit_freshness ();
    test_opaque_dependencies ();
    test_unused_aliases ();
    test_views ();
    test_inheritance ();
    test_residual_application ();
    test_functor_requirements ();
    test_higher_order_application ();
    test_callable_mask_variance ();
    test_sealed_constructor_outputs ();
    test_concrete_module_formal ();
    test_concrete_functor_formal ()
  with
  | () -> ()
  | exception Util.Error.Msg errors ->
      failwith (String.concat ~sep:"\n" (List.map errors ~f:Util.Error.to_string))
