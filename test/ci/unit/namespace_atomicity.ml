open Base
open Raven
open Ast
module Analysis = Frontend.AtomicityAnalysis
module Inference = Frontend.NamespaceInference

let id name = Ident.make Util.Loc.dummy name 0
let qi names = QualIdent.from_list (Predefs.prog_ident :: List.map names ~f:id)
let own names = Callable.MaskHead.Invariant (qi names)
let dependencies names = Callable.MaskHead.Dependencies (qi names)

let run ?(update_draft = Fn.id) source =
  let diagnostics = Util.Diagnostics.create () in
  let lexbuf = Lexing.from_string source in
  Frontend.Lexer.set_file_name lexbuf "namespace_atomicity.rav";
  let _, parsed =
    Driver.parse_cu ~diagnostics ~includes:(Driver.create_includes ()) "."
      Predefs.prog_ident lexbuf
  in
  let tbl =
    SymbolTbl.add_symbol ~diagnostics (Module.ModDef parsed) (SymbolTbl.create ())
  in
  let tbl, typed = Frontend.Typing.check_module ~tbl ~diagnostics parsed in
  let tbl, draft = Rewriter.eval (Inference.infer typed) tbl in
  let draft = update_draft draft in
  let open Rewriter.Syntax in
  let collect = function
    | Module.CallDef ({ call_decl = { call_decl_alias = None; _ }; _ } as call) ->
        let* owner = Rewriter.current_scope_id in
        let name = QualIdent.append owner call.call_decl.call_decl_name in
        let* _ = Rewriter.enter_callable call in
        let* analysis = Analysis.collect_namespace_requirements draft call in
        let* call = Rewriter.exit_callable analysis.callable in
        let* results = Rewriter.current_user_state in
        let+ () = Rewriter.set_user_state (Map.set results ~key:name ~data:analysis) in
        Module.CallDef call
    | symbol -> Rewriter.return symbol
  in
  let _, results =
    Rewriter.eval
      (Rewriter.eval_with_user_state
         ~init:(Map.empty (module QualIdent))
         (let* _ = Rewriter.Module.rec_rewrite_symbols ~f:collect typed in
          Rewriter.current_user_state))
      tbl
  in
  results

let analysis results name = Map.find_exn results (qi name)

let has_separation (analysis : Analysis.namespace_analysis) left right =
  List.exists analysis.separation ~f:(fun requirement ->
      let matches mask head = Callable.mask_equal mask [ (head, []) ] in
      (matches requirement.NamespaceContract.left left && matches requirement.right right)
      || (matches requirement.left right && matches requirement.right left))

let assert_closed_requirements (analysis : Analysis.namespace_analysis) =
  List.iter analysis.separation ~f:(fun requirement ->
      List.iter (requirement.NamespaceContract.left @ requirement.right)
        ~f:(fun (_, args) -> assert (List.is_empty args)))

let test_direct_opens () =
  let results =
    run
      "interface S { inv i(x: Int) inv j(x: Int) }\n\
       module F[P: S] {\n\
       lemma use(ghost x: Int) requires P.i(x) && P.j(x) {\n\
       unfold P.i(x); unfold P.j(x); fold P.j(x); fold P.i(x); } }"
  in
  let result = analysis results [ "F"; "use" ] in
  assert (has_separation result (own [ "F"; "P"; "i" ]) (own [ "F"; "P"; "j" ]));
  assert_closed_requirements result

let test_symbolic_call () =
  let results =
    run
      "interface S { inv i(x: Int) pred p(x: Int) }\n\
       module F[P: S] {\n\
       lemma helper(ghost x: Int) requires P.p(x) {}\n\
       lemma use(ghost x: Int) requires P.i(x) && P.p(x) {\n\
       unfold P.i(x); helper(x); fold P.i(x); } }"
  in
  let result = analysis results [ "F"; "use" ] in
  assert (has_separation result (own [ "F"; "P"; "i" ]) (dependencies [ "F"; "P"; "p" ]));
  assert (Set.mem result.callees (qi [ "F"; "helper" ]));
  assert_closed_requirements result

let rec assertion_specs statement =
  match statement.Stmt.stmt_desc with
  | Basic (Spec (Assert, spec)) -> [ spec ]
  | Block block -> List.concat_map block.block_body ~f:assertion_specs
  | Cond branch -> assertion_specs branch.cond_then @ assertion_specs branch.cond_else
  | Loop loop -> assertion_specs loop.loop_prebody @ assertion_specs loop.loop_postbody
  | Basic _ | StmtExt _ -> []

let assertions statement =
  List.map (assertion_specs statement) ~f:(fun spec -> spec.Stmt.spec_form)

let body (result : Analysis.namespace_analysis) =
  match result.callable.call_def with
  | ProcDef { proc_body = Some body } -> body
  | ProcDef { proc_body = None } | FuncDef _ -> assert false

let mask_assertions result =
  List.filter
    (assertion_specs (body result))
    ~f:(fun spec ->
      List.exists
        (Stmt.spec_error_msg spec (qi [ "use" ]) Util.Loc.dummy)
        ~f:(function Util.Error.Verification Mask, _, _ -> true | _ -> false))

let assert_missing_predicate_credit result =
  assert (
    List.exists (mask_assertions result) ~f:(fun spec ->
        match spec.Stmt.spec_form with
        | Expr.App (Bool false, [], _) -> true
        | App _ | Binder _ -> false))

let rec contains_negation = function
  | Expr.App (Not, _, _) -> true
  | App (_, args, _) -> List.exists args ~f:contains_negation
  | Binder (_, _, _, body, _) -> contains_negation body

let test_same_identity_checks () =
  let results =
    run
      "inv i(x: Int) { true }\n\
       lemma use(ghost x: Int, ghost y: Int) requires i(x) && i(y) {\n\
       unfold i(x); unfold i(y); fold i(y); fold i(x); }"
  in
  let result = analysis results [ "use" ] in
  assert (List.is_empty result.separation);
  assert (List.exists (assertions (body result)) ~f:contains_negation);
  match
    run
      "inv i(x: Int) { true }\n\
       lemma use(ghost x: Int) requires i(x) { unfold i(x); unfold i(x); }"
  with
  | _ -> assert false
  | exception Util.Error.Msg errors ->
      assert (
        List.exists errors ~f:(function
          | Util.Error.Verification Mask, _, _ -> true
          | _ -> false))

let test_branch_union () =
  let results =
    run
      "interface S { inv i(x: Int) pred p(x: Int) pred q(x: Int) }\n\
       module F[P: S] {\n\
       lemma left(ghost x: Int) requires P.p(x) {}\n\
       lemma right(ghost x: Int) requires P.q(x) {}\n\
       lemma use(ghost x: Int, ghost branch: Bool)\n\
       requires P.i(x) && P.p(x) && P.q(x) {\n\
       unfold P.i(x); if (branch) { left(x); } else { right(x); } fold P.i(x); } }"
  in
  let result = analysis results [ "F"; "use" ] in
  List.iter [ "p"; "q" ] ~f:(fun name ->
      assert (
        has_separation result (own [ "F"; "P"; "i" ]) (dependencies [ "F"; "P"; name ])));
  List.iter [ "left"; "right" ] ~f:(fun name ->
      assert (Set.mem result.callees (qi [ "F"; name ])));
  assert_closed_requirements result

let expect_mask_failure source =
  match run source with
  | _ -> assert false
  | exception Util.Error.Msg errors ->
      assert (
        List.exists errors ~f:(function
          | Util.Error.Verification Mask, _, _ -> true
          | _ -> false))

let test_ordinary_branch_credit_intersection () =
  expect_mask_failure
    "inv i(x: Int) { true } inv j(x: Int) { true }\n\
     lemma make(ghost x: Int) ensures j(x) {}\n\
     proc use(ghost x: Int, branch: Bool) requires i(x) {\n\
     unfold i(x); if (branch) { make(x); } else {}\n\
     unfold j(x); fold j(x); fold i(x); }"

let test_ghost_branch_credit_intersection () =
  expect_mask_failure
    "inv j(x: Int) { true }\n\
     lemma make(ghost x: Int) ensures j(x) {}\n\
     lemma use(ghost x: Int, ghost branch: Bool) {\n\
     if (branch) {} else { make(x); } unfold j(x); fold j(x); }"

let test_raw_loops_require_preparation () =
  match run "lemma use() { while (false) {} }" with
  | _ -> assert false
  | exception Util.Error.Msg errors ->
      assert (
        List.exists errors ~f:(function
          | Util.Error.Internal, _, message ->
              String.is_substring message ~substring:"loops to be desugared"
          | _ -> false))

let test_credit_only_requires_separation_when_used () =
  let results =
    run
      "interface S { inv i(x: Int) inv j(x: Int) }\n\
       module F[P: S] {\n\
       lemma make(ghost x: Int) ensures P.j(x) {}\n\
       lemma unused(ghost x: Int) requires P.i(x) {\n\
       unfold P.i(x); make(x); fold P.i(x); }\n\
       lemma allocated(ghost x: Int) requires P.i(x) {\n\
       unfold P.i(x); fold P.j(x); unfold P.j(x); fold P.j(x); fold P.i(x); }\n\
       lemma granted(ghost x: Int) requires P.i(x) {\n\
       unfold P.i(x); make(x); unfold P.j(x); fold P.j(x); fold P.i(x); } }"
  in
  assert (List.is_empty (analysis results [ "F"; "unused" ]).separation);
  List.iter [ "allocated"; "granted" ] ~f:(fun name ->
      let result = analysis results [ "F"; name ] in
      assert (has_separation result (own [ "F"; "P"; "i" ]) (own [ "F"; "P"; "j" ]));
      assert_closed_requirements result)

let test_omitted_implicit_does_not_grant_credit () =
  expect_mask_failure
    "inv i(x: Int) { true }\n\
     lemma make(implicit ghost x: Int) ensures i(x) {}\n\
     lemma use(ghost y: Int) { make(); unfold i(y); fold i(y); }"

let test_predicate_credit_through_abstract_calls () =
  let results =
    run
      "interface Counter {\n\
       pred valid(c: Int, v: Int)\n\
       lemma create(ghost c: Int) ensures valid(c, 0)\n\
       lemma increment(ghost c: Int, ghost v: Int)\n\
       requires valid(c, v) ensures valid(c, v + 1)\n\
       lemma get(ghost c: Int, ghost v: Int) requires valid(c, v)\n\
       }\n\
       module Client[C: Counter] {\n\
       lemma use(ghost c: Int) {\n\
       C.create(c); C.increment(c, 0); C.get(c, 0 + 1);\n\
       } }"
  in
  let result = analysis results [ "Client"; "use" ] in
  assert (List.is_empty (mask_assertions result));
  assert (Set.mem result.callees (qi [ "Client"; "C"; "create" ]));
  assert (Set.mem result.callees (qi [ "Client"; "C"; "increment" ]));
  assert (Set.mem result.callees (qi [ "Client"; "C"; "get" ]))

let test_invariant_dependencies_granted_through_calls () =
  let results =
    run
      "interface S { inv i(x: Int) }\n\
       module F[P: S] {\n\
       lemma make(ghost x: Int) ensures P.i(x) {}\n\
       lemma need(ghost x: Int) requires P.i(x) {}\n\
       lemma use(ghost x: Int) { make(x); need(x); } }"
  in
  assert (List.is_empty (mask_assertions (analysis results [ "F"; "use" ])))

let test_predicate_credit_dropped_after_assignment () =
  let results =
    run
      "interface Counter { pred valid(c: Int, v: Int) }\n\
       module Client[C: Counter] {\n\
       lemma create(ghost c: Int) ensures C.valid(c, 0) {}\n\
       lemma get(ghost c: Int) requires C.valid(c, 0) {}\n\
       lemma use(ghost c: Int) {\n\
       ghost var current: Int := c;\n\
       create(current); current := current + 1; get(current);\n\
       } }"
  in
  assert_missing_predicate_credit (analysis results [ "Client"; "use" ])

let test_predicate_credit_intersects_at_branch_join () =
  let results =
    run
      "interface Counter { pred valid(c: Int, v: Int) }\n\
       module Client[C: Counter] {\n\
       lemma create(ghost c: Int) ensures C.valid(c, 0) {}\n\
       lemma get(ghost c: Int) requires C.valid(c, 0) {}\n\
       lemma use(ghost c: Int, ghost branch: Bool) {\n\
       if (branch) { create(c); } else {} get(c);\n\
       } }"
  in
  assert_missing_predicate_credit (analysis results [ "Client"; "use" ])

let test_predicate_credit_needs_implicit_actual () =
  let results =
    run
      "interface Counter { pred valid(c: Int) }\n\
       module Client[C: Counter] {\n\
       lemma create(implicit ghost c: Int) ensures C.valid(c) {}\n\
       lemma get(ghost c: Int) requires C.valid(c) {}\n\
       lemma use(ghost c: Int) { create(); get(c); }\n\
       }"
  in
  assert_missing_predicate_credit (analysis results [ "Client"; "use" ])

let test_predicate_opens_does_not_restore_credit () =
  let update_draft (draft : Inference.t) =
    let pass = Option.value_exn (Inference.callable draft (qi [ "Client"; "pass" ])) in
    assert (List.is_empty pass.grants);
    draft
  in
  let _ =
    run ~update_draft
      "interface Counter { pred valid(c: Int) }\n\
       module Client[C: Counter] {\n\
       lemma pass(ghost c: Int)\n\
       requires C.valid(c) ensures C.valid(c) opens {} {}\n\
       }"
  in
  ()

let test_granted_predicate_under_open_invariant () =
  let results =
    run
      "interface S { inv i(x: Int) pred p(x: Int) }\n\
       module F[P: S] {\n\
       lemma make(ghost x: Int) ensures P.p(x) {}\n\
       lemma need(ghost x: Int) requires P.p(x) {}\n\
       lemma use(ghost x: Int) requires P.i(x) {\n\
       unfold P.i(x); make(x); need(x); fold P.i(x);\n\
       } }"
  in
  let result = analysis results [ "F"; "use" ] in
  assert (List.is_empty (mask_assertions result));
  assert (has_separation result (own [ "F"; "P"; "i" ]) (dependencies [ "F"; "P"; "p" ]));
  assert_closed_requirements result

let test_call_kinds () =
  List.iter
    [
      ("proc", "requires", "helper(x)");
      ("atomic proc", "requires", "helper(x)");
      ("proc", "atomic requires", "helper(x)");
      ("proc", "requires", "spawn helper(x)");
    ]
    ~f:(fun (kind, requires, call) ->
      let source =
        Printf.sprintf
          "interface S { inv i(x: Int) pred p(x: Int) }\n\
           module F[P: S] { %s helper(ghost x: Int) %s P.p(x) {}\n\
           proc use(ghost x: Int) requires P.i(x) && P.p(x) {\n\
           atomic { unfold P.i(x); %s; fold P.i(x); } } }"
          kind requires call
      in
      let result = analysis (run source) [ "F"; "use" ] in
      assert (
        has_separation result (own [ "F"; "P"; "i" ]) (dependencies [ "F"; "P"; "p" ]));
      assert_closed_requirements result)

let test_recursive_call_edges () =
  let results = run "lemma first() { second(); } lemma second() { first(); }" in
  assert (Set.mem (analysis results [ "first" ]).callees (qi [ "second" ]));
  assert (Set.mem (analysis results [ "second" ]).callees (qi [ "first" ]))

let test_summary_substitution_preserves_conflicts () =
  let update_draft (draft : Inference.t) =
    let callables =
      Map.update draft.callables
        (qi [ "F"; "helper" ])
        ~f:(fun previous ->
          let summary = Option.value_exn previous in
          {
            summary with
            NamespaceContract.separation =
              [
                {
                  left = [ (own [ "F"; "P"; "i" ], []) ];
                  right = [ (own [ "F"; "P"; "j" ], []) ];
                  loc = Util.Loc.dummy;
                };
              ];
          })
    in
    { draft with callables }
  in
  let results =
    run ~update_draft
      "inv leaf(x: Int) { true }\n\
       interface S { inv i(x: Int) inv j(x: Int) }\n\
       module Actual: S { inv i(x: Int) = leaf inv j(x: Int) = leaf }\n\
       module F[P: S] { lemma helper() {} }\n\
       module Instance = F[Actual]\n\
       lemma use() { Instance.helper(); }"
  in
  let result = analysis results [ "use" ] in
  assert (has_separation result (own [ "leaf" ]) (own [ "leaf" ]));
  assert_closed_requirements result

let () =
  match
    test_direct_opens ();
    test_symbolic_call ();
    test_same_identity_checks ();
    test_branch_union ();
    test_summary_substitution_preserves_conflicts ();
    test_ordinary_branch_credit_intersection ();
    test_credit_only_requires_separation_when_used ();
    test_omitted_implicit_does_not_grant_credit ();
    test_predicate_credit_through_abstract_calls ();
    test_invariant_dependencies_granted_through_calls ();
    test_predicate_credit_dropped_after_assignment ();
    test_predicate_credit_intersects_at_branch_join ();
    test_predicate_credit_needs_implicit_actual ();
    test_predicate_opens_does_not_restore_credit ();
    test_granted_predicate_under_open_invariant ();
    test_call_kinds ();
    test_recursive_call_edges ();
    test_ghost_branch_credit_intersection ();
    test_raw_loops_require_preparation ()
  with
  | () -> ()
  | exception Util.Error.Msg errors ->
      failwith (String.concat ~sep:"\n" (List.map errors ~f:Util.Error.to_string))
