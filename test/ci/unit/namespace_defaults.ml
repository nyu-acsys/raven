open Base
open Raven
open Ast
module Closure = Frontend.NamespaceClosure
module Inference = Frontend.NamespaceInference
module Realization = Frontend.NamespaceRealization

let id name = Ident.make Util.Loc.dummy name 0
let qi names = QualIdent.from_list (Predefs.prog_ident :: List.map names ~f:id)

let parse source =
  let diagnostics = Util.Diagnostics.create () in
  let lexbuf = Lexing.from_string source in
  Frontend.Lexer.set_file_name lexbuf "namespace_defaults.rav";
  let _, parsed =
    Driver.parse_cu ~diagnostics ~includes:(Driver.create_includes ()) "."
      Predefs.prog_ident lexbuf
  in
  let tbl =
    SymbolTbl.add_symbol ~diagnostics (Module.ModDef parsed) (SymbolTbl.create ())
  in
  let tbl, typed = Frontend.Typing.check_module ~tbl ~diagnostics parsed in
  (tbl, typed)

let elaborate source =
  let tbl, typed = parse source in
  Rewriter.eval (Closure.elaborate typed) tbl

let validate source =
  let tbl, typed = parse source in
  let tbl, collected = Rewriter.eval (Closure.collect typed) tbl in
  let tbl, draft = Rewriter.eval (Closure.close collected) tbl in
  let tbl, frozen = Rewriter.eval (Closure.freeze draft collected.program) tbl in
  snd (Rewriter.eval (Realization.validate ~draft frozen) tbl)

let module_summary = function
  | NamespaceContract.Module summary -> summary
  | Functor _ -> assert false

let contract program =
  Option.value_exn program.Module.mod_decl.mod_decl_mask_contract |> module_summary

let member summary name =
  List.Assoc.find_exn summary.NamespaceContract.modules (id name) ~equal:Ident.equal

let callable summary name =
  List.Assoc.find_exn summary.NamespaceContract.callables (id name) ~equal:Ident.equal

let argument summary name =
  Expr.from_var_decl (List.hd_exn (callable summary name).formals)

let own names args = Callable.invariant_mask_entry (qi names) args
let deps names args = (Callable.MaskHead.Dependencies (qi names), args)
let assert_mask actual expected = assert (Callable.mask_equal actual expected)

let test_direct_and_abstract_invariants () =
  let _, frozen =
    elaborate
      "inv concrete(x: Int) { true }\n\
       lemma direct(ghost x: Int) requires concrete(x) {}\n\
       interface Sig { inv abstract(x: Int)\n\
       lemma use(ghost x: Int) requires abstract(x) }"
  in
  let root = contract frozen in
  let x = argument root "direct" in
  assert_mask (callable root "direct").requires [ own [ "concrete" ] [ x ] ];
  let signature = module_summary (member root "Sig") in
  let x = argument signature "use" in
  assert_mask (callable signature "use").requires [ own [ "Sig"; "abstract" ] [ x ] ]

let test_visible_and_opaque_predicates () =
  let _, frozen =
    elaborate
      "inv leaf(x: Int) { true }\n\
       pred visible(x: Int) { leaf(x) }\n\
       lemma local(ghost x: Int) requires visible(x) {}\n\
       interface Sig { pred opaque(x: Int)\n\
       lemma default(ghost x: Int) requires opaque(x)\n\
       lemma explicit(ghost x: Int) requires opaque(x) opens opaque(x) }"
  in
  let root = contract frozen in
  let x = argument root "local" in
  assert_mask (callable root "local").requires [ own [ "leaf" ] [ x ] ];
  let signature = module_summary (member root "Sig") in
  assert_mask (callable signature "default").requires [];
  let x = argument signature "explicit" in
  assert_mask (callable signature "explicit").requires [ deps [ "Sig"; "opaque" ] [ x ] ]

let test_interface_budget_and_repeated_contract () =
  let source body =
    "inv hidden(x: Int) { true }\n\
     interface Sig { pred p(x: Int)\n\
     lemma use(ghost x: Int) requires p(x) }\n\
     module Actual: Sig { pred p(x: Int) { hidden(x) }\n\
     lemma use(ghost x: Int) requires p(x) { " ^ body ^ " } }"
  in
  let _, frozen = elaborate (source "") in
  let root = contract frozen in
  let signature = module_summary (member root "Sig") in
  let actual = module_summary (member root "Actual") in
  assert_mask (callable signature "use").requires [];
  assert_mask (callable actual "use").requires [];
  ignore (validate (source "") : Module.t);
  match validate (source "unfold hidden(x); fold hidden(x);") with
  | _ -> failwith "Expected the inherited namespace budget to reject hidden"
  | exception Util.Error.Msg errors ->
      assert (
        List.exists errors ~f:(function
          | Util.Error.Verification Mask, _, _ -> true
          | Util.Error.Type, _, message ->
              String.is_substring (String.lowercase message) ~substring:"namespace"
          | _ -> false))

let test_opaque_grant_provenance () =
  let _, frozen =
    elaborate
      "interface Sig { pred p(x: Int)\n\
       lemma fresh(ghost x: Int) ensures p(x)\n\
       lemma relay(ghost x: Int) requires p(x) ensures p(x) }"
  in
  let signature = module_summary (member (contract frozen) "Sig") in
  let x = argument signature "fresh" in
  assert_mask (callable signature "fresh").grants [ deps [ "Sig"; "p" ] [ x ] ];
  assert_mask (callable signature "relay").requires [];
  assert_mask (callable signature "relay").grants []

let test_parameter_substitution () =
  let tbl, typed =
    parse
      "inv leaf(x: Int) { true }\n\
       interface Sig { inv i(x: Int) pred p(x: Int) }\n\
       module Actual: Sig { inv i(x: Int) = leaf pred p(x: Int) { leaf(x) } }\n\
       module F[P: Sig] { lemma use(ghost x: Int)\n\
       requires P.i(x) && P.p(x) {}\n\
       lemma full(ghost x: Int) requires P.p(x) opens P.p(x) {} }\n\
       module Applied = F[Actual]"
  in
  let tbl, collected = Rewriter.eval (Closure.collect typed) tbl in
  let tbl, draft = Rewriter.eval (Closure.close collected) tbl in
  let _, frozen = Rewriter.eval (Closure.freeze draft collected.program) tbl in
  let root = contract frozen in
  let functor_result =
    match member root "F" with
    | NamespaceContract.Functor summary -> module_summary summary.result
    | Module _ -> assert false
  in
  let x = argument functor_result "use" in
  assert_mask (callable functor_result "use").requires [ own [ "F"; "P"; "i" ] [ x ] ];
  let x = argument functor_result "full" in
  assert_mask (callable functor_result "full").requires [ deps [ "F"; "P"; "p" ] [ x ] ];
  List.iter [ "use"; "full" ] ~f:(fun name ->
      let _, summary =
        Rewriter.eval
          (Rewriter.in_scope_of
             (qi [ "Applied"; name ])
             (Inference.find_callable draft (qi [ "Applied"; name ])))
          tbl
      in
      let summary = Option.value_exn summary in
      let x = Expr.from_var_decl (List.hd_exn summary.formals) in
      assert_mask summary.requires [ own [ "leaf" ] [ x ] ])

let test_module_parameter_projections () =
  ignore
    (validate
       "interface Element {} module Value: Element {}\n\
        interface Base[E: Element] { lemma ping() }\n\
        module Concrete: Base[Value] { lemma ping() {} }\n\
        module Generic[X: Element]: Base[X] { lemma ping() {} }\n\
        module Hidden :> Base = Generic"
      : Module.t);
  ignore
    (validate
       "interface Element { inv marker() }\n\
        interface Carrier { module Part: Element }\n\
        module Maker[Part: Element]: Carrier {}"
      : Module.t)

let test_required_nested_member_still_checked () =
  let tbl, _ = parse "module Empty {}" in
  let empty : NamespaceContract.module_summary =
    { namespaces = []; separation = []; callables = []; modules = [] }
  in
  let expected =
    NamespaceContract.Module
      { empty with modules = [ (id "Part", NamespaceContract.Module empty) ] }
  in
  let actual = NamespaceContract.Module empty in
  let path = qi [ "Empty" ] in
  match
    Rewriter.eval
      (Rewriter.eval_with_user_state
         ~init:(Map.empty (module QualIdent))
         (Realization.compatible ~declarations:[] ~owner:path ~loc:Util.Loc.dummy
            Realization.empty_environment ~actual_path:path ~expected_path:path
            ~established:true actual expected))
      tbl
  with
  | _ -> failwith "A real nested member was omitted"
  | exception Util.Error.Msg errors ->
      assert (
        List.exists errors ~f:(function
          | Util.Error.Type, _, message ->
              String.is_substring message ~substring:"nested module summary is missing"
          | _ -> false))

let () =
  match
    test_direct_and_abstract_invariants ();
    test_visible_and_opaque_predicates ();
    test_interface_budget_and_repeated_contract ();
    test_opaque_grant_provenance ();
    test_parameter_substitution ();
    test_module_parameter_projections ();
    test_required_nested_member_still_checked ()
  with
  | () -> ()
  | exception Util.Error.Msg errors ->
      failwith (String.concat ~sep:"\n" (List.map errors ~f:Util.Error.to_string))
