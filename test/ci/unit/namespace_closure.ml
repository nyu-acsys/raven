open Base
open Raven
open Ast
module Closure = Frontend.NamespaceClosure
module Inference = Frontend.NamespaceInference

let id name = Ident.make Util.Loc.dummy name 0
let qi names = QualIdent.from_list (Predefs.prog_ident :: List.map names ~f:id)
let own names = Callable.MaskHead.Invariant (qi names)

let parse ?(root = Predefs.prog_ident) ?(tbl = SymbolTbl.create ()) ?(free = false)
    ?ext_hooks source =
  let diagnostics = Util.Diagnostics.create () in
  let lexbuf = Lexing.from_string source in
  Frontend.Lexer.set_file_name lexbuf "namespace_closure.rav";
  let _, parsed =
    Driver.parse_cu ~diagnostics ~includes:(Driver.create_includes ()) "." root lexbuf
  in
  let parsed = if free then Module.set_unit_free parsed else parsed in
  let tbl = SymbolTbl.add_symbol ~diagnostics (Module.ModDef parsed) tbl in
  let tbl, typed = Frontend.Typing.check_module ?ext_hooks ~tbl ~diagnostics parsed in
  (diagnostics, tbl, typed)

let has_separation requirements left right =
  let matches mask head = Callable.mask_equal mask [ (head, []) ] in
  List.exists requirements ~f:(fun requirement ->
      (matches requirement.NamespaceContract.left left && matches requirement.right right)
      || (matches requirement.left right && matches requirement.right left))

let module_summary = function
  | NamespaceContract.Module summary -> summary
  | Functor _ -> assert false

let child summary name =
  List.Assoc.find_exn summary.NamespaceContract.modules (id name) ~equal:Ident.equal

let call summary name =
  List.Assoc.find_exn summary.NamespaceContract.callables (id name) ~equal:Ident.equal

let contract program = Option.value_exn program.Module.mod_decl.mod_decl_mask_contract

let cyclic_source =
  "interface S { inv i(x: Int) inv j(x: Int) }\n\
   module F[P: S] {\n\
   lemma first(ghost x: Int) requires P.i(x) && P.j(x) { second(x); }\n\
   lemma second(ghost x: Int) requires P.i(x) && P.j(x) {\n\
   unfold P.i(x); unfold P.j(x); fold P.j(x); fold P.i(x); first(x); } }"

let test_cycle_and_freeze () =
  let _, tbl, typed = parse cyclic_source in
  let tbl, collected = Rewriter.eval (Closure.collect typed) tbl in
  let bodies =
    Map.map collected.analyses ~f:(fun analysis ->
        analysis.Frontend.AtomicityAnalysis.callable)
  in
  let count = Map.length collected.analyses in
  let tbl, closed = Rewriter.eval (Closure.close collected) tbl in
  assert (Map.length collected.analyses = count);
  assert (
    Map.equal phys_equal bodies
      (Map.map collected.analyses ~f:(fun analysis ->
           analysis.Frontend.AtomicityAnalysis.callable)));
  List.iter [ "first"; "second" ] ~f:(fun name ->
      let summary = Option.value_exn (Inference.callable closed (qi [ "F"; name ])) in
      assert (
        has_separation summary.separation (own [ "F"; "P"; "i" ]) (own [ "F"; "P"; "j" ])));
  let _, frozen = Rewriter.eval (Closure.freeze closed collected.program) tbl in
  let root = module_summary (contract frozen) in
  assert (List.is_empty root.separation);
  match child root "F" with
  | Module _ -> assert false
  | Functor summary ->
      assert (List.length summary.parameters = 1);
      let parameter = module_summary (snd (List.hd_exn summary.parameters)) in
      assert (List.length parameter.namespaces = 2);
      let result = module_summary summary.result in
      List.iter [ "first"; "second" ] ~f:(fun name ->
          assert (
            has_separation (call result name).separation
              (own [ "F"; "P"; "i" ])
              (own [ "F"; "P"; "j" ])))

let test_instantiated_callee () =
  let source =
    cyclic_source
    ^ "\n\
       inv left(x: Int) { true } inv right(x: Int) { true }\n\
       module Actual: S { inv i(x: Int) = left inv j(x: Int) = right }\n\
       module Instance = F[Actual]\n\
       lemma use(ghost x: Int) requires left(x) && right(x) { Instance.first(x); }"
  in
  let _, tbl, typed = parse source in
  let _, frozen = Rewriter.eval (Closure.elaborate typed) tbl in
  let summary = call (module_summary (contract frozen)) "use" in
  assert (has_separation summary.separation (own [ "left" ]) (own [ "right" ]))

let test_reflexive_instantiation () =
  let source =
    cyclic_source
    ^ "\n\
       inv leaf(x: Int) { true }\n\
       module Actual: S { inv i(x: Int) = leaf inv j(x: Int) = leaf }\n\
       module Instance = F[Actual]\n\
       lemma use(ghost x: Int) requires leaf(x) { Instance.first(x); }"
  in
  let _, tbl, typed = parse source in
  let _, frozen = Rewriter.eval (Closure.elaborate typed) tbl in
  let summary = call (module_summary (contract frozen)) "use" in
  assert (has_separation summary.separation (own [ "leaf" ]) (own [ "leaf" ]))

let test_nested_and_unit_signatures () =
  let _, tbl, typed =
    parse
      "module Outer { module Inner { inv i() { true } lemma use() {} } } module \
       Factory() { lemma make() {} }"
  in
  let _, frozen = Rewriter.eval (Closure.elaborate typed) tbl in
  let root = module_summary (contract frozen) in
  let inner = module_summary (child (module_summary (child root "Outer")) "Inner") in
  assert (List.length inner.namespaces = 1);
  ignore (call inner "use" : NamespaceContract.callable_summary);
  match child root "Factory" with
  | Module _ -> assert false
  | Functor summary ->
      assert (List.is_empty summary.parameters);
      ignore
        (call (module_summary summary.result) "make" : NamespaceContract.callable_summary)

let test_prior_compilation_unit () =
  let _, tbl, library =
    parse ~root:(id "Previous")
      "inv leaf(x: Int) { true } pred wrapper(x: Int) { leaf(x) } lemma helper(ghost x: \
       Int) requires wrapper(x) {}"
  in
  let tbl, _ = Rewriter.eval (Closure.elaborate library) tbl in
  let _, tbl, typed =
    parse ~tbl
      "lemma use(ghost x: Int) requires Previous.wrapper(x) { Previous.helper(x); }"
  in
  let _, frozen = Rewriter.eval (Closure.elaborate typed) tbl in
  let use = call (module_summary (contract frozen)) "use" in
  let previous_leaf = QualIdent.from_list [ id "Previous"; id "leaf" ] in
  assert (
    List.exists use.requires ~f:(fun (head, _) ->
        QualIdent.equal (Callable.mask_head_name head) previous_leaf));
  assert (
    not
      (List.exists use.requires ~f:(fun (head, _) ->
           QualIdent.equal
             (Callable.mask_head_name head)
             (QualIdent.from_list [ id "Previous"; id "wrapper" ]))))

let test_prior_instantiated_compilation_unit () =
  let _, tbl, library =
    parse ~root:(id "Previous")
      "interface S { inv i(x: Int) }\n\
       module F[P: S] { pred wrapper(x: Int) { P.i(x) }\n\
       lemma helper(ghost x: Int) requires wrapper(x) {} }\n\
       inv leaf(x: Int) { true }\n\
       module Actual: S { inv i(x: Int) = leaf }\n\
       module Instance = F[Actual]"
  in
  let tbl, _ = Rewriter.eval (Closure.elaborate library) tbl in
  let _, tbl, typed =
    parse ~tbl
      "lemma use(ghost x: Int) requires Previous.Instance.wrapper(x) { \
       Previous.Instance.helper(x); }"
  in
  let _, frozen = Rewriter.eval (Closure.elaborate typed) tbl in
  let use = call (module_summary (contract frozen)) "use" in
  let previous_leaf = QualIdent.from_list [ id "Previous"; id "leaf" ] in
  match use.requires with
  | [ (Callable.MaskHead.Invariant name, [ _ ]) ] ->
      assert (QualIdent.equal name previous_leaf)
  | _ -> assert false

let test_module_binding_signatures () =
  let _, tbl, typed =
    parse
      "module Original { inv i() { true } lemma use() {} }\n\
       module Alias = Original\n\
       module Factory() { inv j() { true } lemma make() {} }\n\
       module Created = Factory()\n\
       module FactoryAlias = Factory"
  in
  let _, frozen = Rewriter.eval (Closure.elaborate typed) tbl in
  let root = module_summary (contract frozen) in
  let alias = module_summary (child root "Alias") in
  assert (List.length alias.namespaces = 1);
  ignore (call alias "use" : NamespaceContract.callable_summary);
  let created = module_summary (child root "Created") in
  assert (List.length created.namespaces = 1);
  ignore (call created "make" : NamespaceContract.callable_summary);
  match child root "FactoryAlias" with
  | NamespaceContract.Module _ -> assert false
  | Functor summary ->
      assert (List.is_empty summary.parameters);
      ignore
        (call (module_summary summary.result) "make" : NamespaceContract.callable_summary)

let rec assertions statement =
  match statement.Stmt.stmt_desc with
  | Basic (Spec (Assert, spec)) -> [ spec.spec_form ]
  | Block block -> List.concat_map block.block_body ~f:assertions
  | Cond branch -> assertions branch.cond_then @ assertions branch.cond_else
  | Loop loop -> assertions loop.loop_prebody @ assertions loop.loop_postbody
  | Basic _ | StmtExt _ -> []

let test_aliases_exposed_by_imported_equations () =
  let _, tbl, library =
    parse ~root:(id "Previous")
      "interface S { inv i(x: Int) }\n\
       module F[P: S] { pred wrapper(x: Int) { P.i(x) } }\n\
       inv leaf(x: Int) { true }\n\
       module Actual: S { inv i(x: Int) = leaf }\n\
       module Instance = F[Actual]\n\
       interface Predicate { pred p(x: Int) }\n\
       module Wrapped: Predicate { pred p(x: Int) { Instance.wrapper(x) } }\n\
       module G[P: Predicate] { lemma helper(ghost x: Int) requires P.p(x) {} }\n\
       module Action = G[Wrapped]"
  in
  let tbl, _ = Rewriter.eval (Closure.elaborate library) tbl in
  let _, tbl, program =
    parse ~tbl
      "lemma use(ghost x: Int) requires Previous.Wrapped.p(x) { \
       Previous.Action.helper(x); }"
  in
  let _, collected = Rewriter.eval (Closure.collect program) tbl in
  let use = Map.find_exn collected.analyses (qi [ "use" ]) in
  let body =
    match use.callable.call_def with
    | ProcDef { proc_body = Some body } -> body
    | FuncDef _ | ProcDef { proc_body = None } -> assert false
  in
  assert (List.is_empty (assertions body))

let test_realization_preserves_bodies () =
  let _, tbl, typed = parse cyclic_source in
  let tbl, collected = Rewriter.eval (Closure.collect typed) tbl in
  let tbl, draft = Rewriter.eval (Closure.close collected) tbl in
  let tbl, frozen = Rewriter.eval (Closure.freeze draft collected.program) tbl in
  let bodies program =
    let rec gather owner program bodies =
      List.fold program.Module.mod_def ~init:bodies ~f:(fun bodies -> function
        | Module.SymbolDef (CallDef call) ->
            Map.set bodies
              ~key:(QualIdent.append owner call.call_decl.call_decl_name)
              ~data:call.call_def
        | SymbolDef (ModDef child) ->
            gather (QualIdent.append owner child.mod_decl.mod_decl_name) child bodies
        | SymbolDef
            (ModInst _ | TypeDef _ | VarDef _ | FieldDef _ | ConstrDef _ | DestrDef _)
        | Import _ ->
            bodies)
    in
    gather
      (QualIdent.from_ident program.Module.mod_decl.mod_decl_name)
      program
      (Map.empty (module QualIdent))
  in
  let before = bodies frozen in
  let _, validated =
    Rewriter.eval (Frontend.NamespaceRealization.validate ~draft frozen) tbl
  in
  assert (Map.equal phys_equal before (bodies validated))

let test_conditional_interface_requirements () =
  let _, tbl, typed =
    parse
      "interface Conditional { inv cell(x: Int) pred resource(x: Int) lemma helper(ghost \
       x: Int) requires resource(x) {} lemma use(ghost x: Int) requires cell(x) && \
       resource(x) { unfold cell(x); helper(x); fold cell(x); } }"
  in
  let tbl, collected = Rewriter.eval (Closure.collect typed) tbl in
  let tbl, draft = Rewriter.eval (Closure.close collected) tbl in
  let tbl, frozen = Rewriter.eval (Closure.freeze draft collected.program) tbl in
  let root = module_summary (contract frozen) in
  assert (List.is_empty root.separation);
  let conditional = module_summary (child root "Conditional") in
  assert (not (List.is_empty conditional.separation));
  ignore
    (Rewriter.eval (Frontend.NamespaceRealization.validate ~draft frozen) tbl
      : SymbolTbl.t * Module.t)

let test_standard_library_headers () =
  let ext_hooks = Ext.to_ext_hooks (Ext.module_map Ext.DefaultExt) in
  let source = String.concat ~sep:"\n" (List.map Library.library_sources ~f:snd) in
  let diagnostics, tbl, typed =
    parse ~root:Predefs.lib_ident ~free:true ~ext_hooks source
  in
  let _, frozen =
    Frontend.Elaboration.elaborate_module ~namespace_contracts:true ~ext_hooks ~tbl
      ~diagnostics typed
  in
  ignore (module_summary (contract frozen) : NamespaceContract.module_summary)

let test_forward_header_dependency () =
  let _, tbl, typed = parse "module F[P: S] {} interface S {}" in
  let _, frozen = Rewriter.eval (Closure.elaborate typed) tbl in
  let root = module_summary (contract frozen) in
  match child root "F" with
  | Module _ -> assert false
  | Functor summary -> assert (List.length summary.parameters = 1)

let test_formal_nested_member () =
  let _, tbl, typed =
    parse
      "interface Element { inv value() } interface Container { module E : Element } \
       module Make[E: Element] : Container {}"
  in
  let tbl, collected = Rewriter.eval (Closure.collect typed) tbl in
  let tbl, draft = Rewriter.eval (Closure.close collected) tbl in
  let tbl, frozen = Rewriter.eval (Closure.freeze draft collected.program) tbl in
  let root = module_summary (contract frozen) in
  let result =
    match child root "Make" with
    | Module _ -> assert false
    | Functor summary -> module_summary summary.result
  in
  let element = module_summary (child result "E") in
  assert (List.length element.namespaces = 1);
  ignore (Rewriter.eval (Frontend.NamespaceRealization.validate ~draft frozen) tbl)

let test_pipeline () =
  let ext_hooks = Ext.to_ext_hooks (Ext.module_map Ext.DefaultExt) in
  let diagnostics, tbl, typed = parse "lemma use() { while (false) {} }" in
  let _, frozen =
    Frontend.Elaboration.elaborate_module ~namespace_contracts:true ~ext_hooks ~tbl
      ~diagnostics typed
  in
  let summary = module_summary (contract frozen) in
  assert (List.length summary.callables >= 2)

let () =
  match
    test_cycle_and_freeze ();
    test_instantiated_callee ();
    test_reflexive_instantiation ();
    test_nested_and_unit_signatures ();
    test_prior_compilation_unit ();
    test_prior_instantiated_compilation_unit ();
    test_module_binding_signatures ();
    test_forward_header_dependency ();
    test_formal_nested_member ();
    test_pipeline ();
    test_conditional_interface_requirements ();
    test_realization_preserves_bodies ();
    test_aliases_exposed_by_imported_equations ();
    test_standard_library_headers ()
  with
  | () -> ()
  | exception Util.Error.Msg errors ->
      failwith (String.concat ~sep:"\n" (List.map errors ~f:Util.Error.to_string))
