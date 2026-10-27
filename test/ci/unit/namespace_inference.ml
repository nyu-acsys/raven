open Base
open Raven
open Ast
module Inference = Frontend.NamespaceInference

let parse source =
  let diagnostics = Util.Diagnostics.create () in
  let lexbuf = Lexing.from_string source in
  Frontend.Lexer.set_file_name lexbuf "namespace_inference.rav";
  let _, parsed =
    Driver.parse_cu ~diagnostics ~includes:(Driver.create_includes ()) "."
      Ast.Predefs.prog_ident lexbuf
  in
  let tbl =
    SymbolTbl.add_symbol ~diagnostics (Module.ModDef parsed) (SymbolTbl.create ())
  in
  let symbols, typed = Frontend.Typing.check_module ~tbl ~diagnostics parsed in
  let symbols, draft = Rewriter.eval (Inference.infer typed) symbols in
  let check symbol =
    begin match symbol with
    | Module.ModDef m -> assert (Option.is_none m.mod_decl.mod_decl_mask_contract)
    | CallDef call ->
        assert (Option.is_none call.call_decl.call_decl_needs_mask);
        assert (Option.is_none call.call_decl.call_decl_grants_mask)
    | _ -> ()
    end;
    Rewriter.return symbol
  in
  let _, _ = Rewriter.eval (Rewriter.Module.rec_rewrite_symbols ~f:check typed) symbols in
  assert (Option.is_none typed.mod_decl.mod_decl_mask_contract);
  (symbols, draft)

let id name = Ident.make Util.Loc.dummy name 0
let qi names = QualIdent.from_list (Predefs.prog_ident :: List.map names ~f:id)
let namespace draft name = Option.value_exn (Inference.namespace draft (qi name))
let callable draft name = Option.value_exn (Inference.callable draft (qi name))

let has_mask_entry mask expected =
  List.exists mask ~f:(fun entry -> Callable.mask_equal [ entry ] [ expected ])

let own name args = Callable.invariant_mask_entry (qi name) args
let dependency name args = (Callable.MaskHead.Dependencies (qi name), args)

let argument symbols name =
  let _, call =
    Rewriter.eval
      (Rewriter.in_scope_of (qi name) (Rewriter.find_and_reify_callable (qi name)))
      symbols
  in
  Expr.from_var_decl (List.hd_exn call.call_decl.call_decl_formals)

let test_concrete_resource_expansion () =
  let symbols, draft =
    parse
      "inv leaf(x: Int) { true }\n\
       pred wrapper(x: Int) { leaf(x) }\n\
       proc use(x: Int) requires wrapper(x) ensures leaf(x) { }"
  in
  begin match (namespace draft [ "leaf" ]).NamespaceContract.definition with
  | NamespaceContract.Defined [] -> ()
  | NamespaceContract.Abstract | NamespaceContract.Defined _ -> assert false
  end;
  let wrapper = namespace draft [ "wrapper" ] in
  let x = argument symbols [ "wrapper" ] in
  begin match wrapper.definition with
  | Defined body ->
      assert (has_mask_entry body (own [ "leaf" ] [ x ]));
      assert (has_mask_entry body (dependency [ "leaf" ] [ x ]))
  | NamespaceContract.Abstract -> assert false
  end;
  let x = argument symbols [ "use" ] in
  let use = callable draft [ "use" ] in
  assert (has_mask_entry use.requires (own [ "leaf" ] [ x ]));
  assert (not (has_mask_entry use.requires (dependency [ "leaf" ] [ x ])));
  assert (has_mask_entry use.grants (own [ "leaf" ] [ x ]));
  assert (has_mask_entry use.grants (dependency [ "leaf" ] [ x ]))

let test_opaque_formal_namespace () =
  let symbols, draft =
    parse
      "interface Sig { pred p(x: Int) inv i(x: Int) }\n\
       module F[P: Sig] {\n\
       proc use(x: Int) requires P.p(x) && P.i(x) ensures P.i(x) {}\n\
       }"
  in
  let formal_predicate = namespace draft [ "F"; "P"; "p" ] in
  assert (Poly.equal formal_predicate.definition NamespaceContract.Abstract);
  let x = argument symbols [ "F"; "use" ] in
  let use = callable draft [ "F"; "use" ] in
  assert (Callable.mask_equal use.requires [ own [ "F"; "P"; "i" ] [ x ] ]);
  assert (Callable.mask_equal use.grants [ own [ "F"; "P"; "i" ] [ x ] ])

let test_alias_does_not_create_identity () =
  let _, draft =
    parse "inv leaf(x: Int) { true }\nmodule Alias { inv shared(x: Int) = leaf }"
  in
  assert (Option.is_none (Inference.namespace draft (qi [ "Alias"; "shared" ])));
  assert (Option.is_some (Inference.namespace draft (qi [ "leaf" ])))

let test_instantiated_equation_alias () =
  let symbols, draft =
    parse
      "inv leaf(x: Int) { true }\n\
       interface Sig { inv i(x: Int) }\n\
       module Actual: Sig { inv i(x: Int) = leaf }\n\
       module F[P: Sig] { pred wrapper(x: Int) { P.i(x) } }\n\
       module Instance = F[Actual]\n\
       proc use(x: Int) requires Instance.wrapper(x) ensures leaf(x) {}"
  in
  let x = argument symbols [ "use" ] in
  let use = callable draft [ "use" ] in
  assert (Callable.mask_equal use.requires [ own [ "leaf" ] [ x ] ]);
  assert (
    Callable.mask_equal use.grants [ own [ "leaf" ] [ x ]; dependency [ "leaf" ] [ x ] ])

let test_existential_required_prefix () =
  let symbols, draft =
    parse
      "inv leaf(x: Int, y: Int) { true }\n\
       pred wrapper(x: Int) { exists y: Int :: leaf(x, y) }\n\
       proc use(x: Int) requires wrapper(x) {}"
  in
  let x = argument symbols [ "use" ] in
  assert (Callable.mask_equal (callable draft [ "use" ]).requires [ own [ "leaf" ] [ x ] ])

let test_grants_never_widen () =
  let symbols, draft =
    parse
      "inv leaf(x: Int) { true }\n\
       proc exact(x: Int) ensures leaf(x) {}\n\
       proc hidden() ensures exists x: Int :: leaf(x) {}\n\
       proc returned() returns (x: Int) ensures leaf(x) {}"
  in
  let x = argument symbols [ "exact" ] in
  assert (
    Callable.mask_equal (callable draft [ "exact" ]).grants
      [ own [ "leaf" ] [ x ]; dependency [ "leaf" ] [ x ] ]);
  assert (List.is_empty (callable draft [ "hidden" ]).grants);
  let x =
    let _, call =
      Rewriter.eval (Rewriter.find_and_reify_callable (qi [ "returned" ])) symbols
    in
    Expr.from_var_decl (List.hd_exn call.call_decl.call_decl_returns)
  in
  assert (
    Callable.mask_equal (callable draft [ "returned" ]).grants
      [ own [ "leaf" ] [ x ]; dependency [ "leaf" ] [ x ] ])

let test_opens_does_not_restore_omitted_credit () =
  let _, draft =
    parse
      "interface Sig { pred p(x: Int) inv i(x: Int) }\n\
       module F[P: Sig] {\n\
       proc use(x: Int) requires P.p(x) ensures P.i(x) opens {} {}\n\
       }"
  in
  let use = callable draft [ "F"; "use" ] in
  assert (List.is_empty use.requires);
  assert (List.is_empty use.grants)

let test_exact_predicate_grants () =
  let symbols, draft =
    parse
      "interface Sig { pred p(x: Int, y: Int) }\n\
       module F[P: Sig] {\n\
       proc exact(x: Int, y: Int) ensures P.p(x, y) {}\n\
       proc hidden(x: Int) ensures exists y: Int :: P.p(x, y) {}\n\
       proc returned() returns (x: Int) ensures P.p(x, 0) {}\n\
       proc logical(implicit ghost x: Int) atomic ensures P.p(x, 0) {}\n\
       proc omitted(x: Int) requires P.p(x, 0) ensures P.p(x, 0) opens {} {} }"
  in
  let _, exact =
    Rewriter.eval
      (Rewriter.in_scope_of
         (qi [ "F"; "exact" ])
         (Rewriter.find_and_reify_callable (qi [ "F"; "exact" ])))
      symbols
  in
  let args = List.map exact.call_decl.call_decl_formals ~f:Expr.from_var_decl in
  assert (
    Callable.mask_equal (callable draft [ "F"; "exact" ]).grants
      [ dependency [ "F"; "P"; "p" ] args ]);
  List.iter [ "hidden"; "logical"; "omitted" ] ~f:(fun name ->
      assert (List.is_empty (callable draft [ "F"; name ]).grants));
  let _, returned =
    Rewriter.eval
      (Rewriter.in_scope_of
         (qi [ "F"; "returned" ])
         (Rewriter.find_and_reify_callable (qi [ "F"; "returned" ])))
      symbols
  in
  let x = Expr.from_var_decl (List.hd_exn returned.call_decl.call_decl_returns) in
  assert (
    Callable.mask_equal (callable draft [ "F"; "returned" ]).grants
      [ dependency [ "F"; "P"; "p" ] [ x; Expr.mk_int 0 ] ])

let test_predicate_grants_remain_symbolic () =
  let symbols, draft =
    parse
      "inv leaf(x: Int) { true }\n\
       pred target(x: Int) { exists y: Int :: leaf(y) }\n\
       pred alias(x: Int) = target\n\
       proc exact(x: Int) ensures alias(x) {}"
  in
  let x = argument symbols [ "exact" ] in
  assert (
    Callable.mask_equal (callable draft [ "exact" ]).grants
      [ dependency [ "target" ] [ x ] ])

let test_atomic_implicit_and_resource_outputs () =
  let symbols, draft =
    parse
      "inv leaf(x: Int; y: Int) { true }\n\
       proc exact(x: Int, ghost y: Int) ensures leaf(x, y) {}\n\
       proc hidden(x: Int) ensures exists y: Int :: leaf(x, y) {}\n\
       proc logical(implicit ghost x: Int)\n\
       atomic requires leaf(x, 0) atomic ensures leaf(x, 0) {}"
  in
  let _, exact =
    Rewriter.eval (Rewriter.find_and_reify_callable (qi [ "exact" ])) symbols
  in
  let args = List.map exact.call_decl.call_decl_formals ~f:Expr.from_var_decl in
  assert (
    Callable.mask_equal (callable draft [ "exact" ]).grants
      [ own [ "leaf" ] args; dependency [ "leaf" ] args ]);
  assert (List.is_empty (callable draft [ "hidden" ]).grants);
  assert (
    Callable.mask_equal (callable draft [ "logical" ]).requires [ own [ "leaf" ] [] ]);
  assert (List.is_empty (callable draft [ "logical" ]).grants)

let () =
  match
    test_concrete_resource_expansion ();
    test_opaque_formal_namespace ();
    test_alias_does_not_create_identity ();
    test_instantiated_equation_alias ();
    test_existential_required_prefix ();
    test_grants_never_widen ();
    test_opens_does_not_restore_omitted_credit ();
    test_exact_predicate_grants ();
    test_predicate_grants_remain_symbolic ();
    test_atomic_implicit_and_resource_outputs ()
  with
  | () -> ()
  | exception Util.Error.Msg errors ->
      failwith (String.concat ~sep:"\n" (List.map errors ~f:Util.Error.to_string))
