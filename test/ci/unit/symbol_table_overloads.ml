open Base
open Raven
open Ast

let id name = Ident.make Util.Loc.dummy name 0
let diagnostics = Util.Diagnostics.create ()
let qi names = QualIdent.from_list (List.map names ~f:id)

let func internal source =
  let call_decl =
    Callable.mk_call_decl ~kind:Func ~name:(id internal) ~loc:Util.Loc.dummy ()
  in
  Module.CallDef
    {
      call_decl = { call_decl with call_decl_source_name = Some (id source) };
      call_def = Callable.FuncDef { func_body = None };
    }

let module_ ?(decl = Module.empty_decl) name symbols =
  Module.ModDef
    {
      mod_decl = { decl with mod_decl_name = id name };
      mod_def = List.map symbols ~f:(fun symbol -> Module.SymbolDef symbol);
    }

let rec register symbol tbl =
  let tbl = SymbolTbl.add_symbol ~diagnostics symbol tbl in
  match symbol with
  | Module.ModDef m ->
      let tbl = SymbolTbl.enter_exn m.mod_decl.mod_decl_name tbl in
      let tbl =
        List.fold m.mod_def ~init:tbl ~f:(fun tbl instr ->
            match instr with
            | Module.SymbolDef symbol -> register symbol tbl
            | Module.Import directive -> SymbolTbl.import ~diagnostics directive tbl)
      in
      SymbolTbl.exit tbl
  | _ -> tbl

let import ?(all = true) name tbl =
  SymbolTbl.import ~diagnostics
    {
      Module.import_name = qi name;
      import_all = all;
      import_prelude = false;
      import_loc = Util.Loc.dummy;
    }
    tbl

let candidates name tbl = SymbolTbl.resolve_and_find_candidates (qi name) tbl

let expect_targets name expected tbl =
  let actual = List.map (candidates name tbl) ~f:(fun (_, target, _, _) -> target) in
  let expected = List.map expected ~f:qi |> List.sort ~compare:QualIdent.compare in
  assert (List.equal QualIdent.equal actual expected)

let base () =
  SymbolTbl.create ()
  |> register (module_ "A" [ func "$a1" "f"; func "$a2" "f" ])
  |> register (module_ "B" [ func "$b" "f" ])
  |> register (module_ "Use" [])

let test_internal_scopes () =
  let tbl = base () in
  expect_targets [ "A"; "f" ] [ [ "A"; "$a1" ]; [ "A"; "$a2" ] ] tbl;
  expect_targets [ "A"; "$a1" ] [ [ "A"; "$a1" ] ] tbl;
  assert (Option.is_none (SymbolTbl.resolve_and_find (qi [ "A"; "f" ]) tbl));
  let tbl = SymbolTbl.enter_exn (id "A") tbl in
  expect_targets [ "f" ] [ [ "A"; "$a1" ]; [ "A"; "$a2" ] ] tbl;
  let first = SymbolTbl.enter_exn (id "$a1") tbl in
  let second = SymbolTbl.enter_exn (id "$a2") tbl in
  assert (
    not
      (QualIdent.equal
         (SymbolTbl.get_scope_id first.tbl_curr)
         (SymbolTbl.get_scope_id second.tbl_curr)))

let test_imports () =
  let run order =
    let tbl = base () |> SymbolTbl.enter_exn (id "Use") in
    let tbl = List.fold order ~init:tbl ~f:(fun tbl name -> import [ name ] tbl) in
    expect_targets [ "f" ] [ [ "A"; "$a1" ]; [ "A"; "$a2" ]; [ "B"; "$b" ] ] tbl;
    assert (List.length (SymbolTbl.find_import_targets (qi [ "f" ]) tbl) = 3);
    let tbl = SymbolTbl.exit tbl in
    expect_targets [ "Use"; "f" ] [] tbl
  in
  run [ "A"; "B"; "A" ];
  run [ "B"; "A"; "B" ];
  let tbl =
    base ()
    |> SymbolTbl.enter_exn (id "Use")
    |> import ~all:false [ "A"; "f" ]
    |> import ~all:false [ "B"; "f" ]
  in
  expect_targets [ "f" ] [ [ "A"; "$a1" ]; [ "A"; "$a2" ]; [ "B"; "$b" ] ] tbl

let test_hiding_and_cache () =
  let tbl = base () |> import [ "A" ] |> SymbolTbl.enter_exn (id "Use") in
  expect_targets [ "f" ] [ [ "A"; "$a1" ]; [ "A"; "$a2" ] ] tbl;
  let tbl = import [ "B" ] tbl in
  expect_targets [ "f" ] [ [ "B"; "$b" ] ] tbl;
  let tbl = register (func "$local1" "f") tbl in
  expect_targets [ "f" ] [ [ "Use"; "$local1" ] ] tbl;
  let tbl = import [ "A" ] tbl |> register (func "$local2" "f") in
  expect_targets [ "f" ] [ [ "Use"; "$local1" ]; [ "Use"; "$local2" ] ] tbl;
  assert (List.is_empty (SymbolTbl.find_import_targets (qi [ "f" ]) tbl))

let test_symbol_replacement () =
  let tbl = base () |> SymbolTbl.enter_exn (id "B") in
  let before = candidates [ "f" ] tbl in
  let original =
    match before with [ (_, _, Module.CallDef call, _) ] -> call | _ -> assert false
  in
  let result = Type.mk_var_decl (id "result") Type.int in
  let updated =
    Module.CallDef
      {
        original with
        call_decl = { original.call_decl with call_decl_returns = [ result ] };
      }
  in
  let tbl = SymbolTbl.set_symbol updated tbl in
  expect_targets [ "f" ] [ [ "B"; "$b" ] ] tbl;
  match candidates [ "f" ] tbl with
  | [ (_, _, Module.CallDef call, _) ] ->
      assert (Type.equal (Callable.return_type call.call_decl) Type.int)
  | _ -> assert false

let instance ?(args = []) ?(abstract = false) ?(sealed = false) ?typ name target =
  Module.ModInst
    {
      mod_inst_name = id name;
      mod_inst_type = qi (Option.value typ ~default:target);
      mod_inst_def =
        (if abstract then None else Some (Module.legacy_application (qi target, args)));
      mod_inst_is_interface = abstract;
      mod_inst_is_free = false;
      mod_inst_is_sealed = sealed;
      mod_inst_shared = [];
      mod_inst_loc = Util.Loc.dummy;
    }

let test_aliases () =
  let tbl = base () |> register (instance "Alias" [ "A" ]) in
  expect_targets [ "Alias"; "f" ] [ [ "A"; "$a1" ]; [ "A"; "$a2" ] ] tbl;
  let tbl = SymbolTbl.enter_exn (id "Use") tbl |> import [ "Alias" ] in
  expect_targets [ "f" ] [ [ "A"; "$a1" ]; [ "A"; "$a2" ] ] tbl;
  List.iter
    [ [ "A"; "Alias" ]; [ "Alias"; "A" ] ]
    ~f:(fun order ->
      let tbl =
        base () |> register (instance "Alias" [ "A" ]) |> SymbolTbl.enter_exn (id "Use")
      in
      let tbl = List.fold order ~init:tbl ~f:(fun tbl name -> import [ name ] tbl) in
      assert (List.length (candidates [ "f" ] tbl) = 2);
      assert (List.length (SymbolTbl.find_import_targets (qi [ "f" ]) tbl) = 2))

let test_parameter_substitution () =
  let interface_decl = { Module.empty_decl with mod_decl_is_interface = true } in
  let formal = instance ~abstract:true "P" [ "I" ] in
  let formal_decl = match formal with Module.ModInst decl -> decl | _ -> assert false in
  let decl =
    {
      Module.empty_decl with
      mod_decl_parameters = Module.NamedParameters [ formal_decl ];
    }
  in
  let tbl =
    SymbolTbl.create ()
    |> register (module_ ~decl:interface_decl "I" [])
    |> register (module_ "Arg" [])
    |> register (module_ ~decl "F" [ formal; func "$f1" "f"; func "$f2" "f" ])
    |> register (instance ~args:[ Module.ModArg (qi [ "Arg" ]) ] "Instance" [ "F" ])
  in
  expect_targets [ "Instance"; "f" ] [ [ "Instance"; "$f1" ]; [ "Instance"; "$f2" ] ] tbl;
  List.iter
    (candidates [ "Instance"; "f" ] tbl)
    ~f:(fun (_, _, _, subst) ->
      assert (SymbolTbl.is_instance subst);
      assert (
        QualIdent.equal
          (QualIdent.requalify (SymbolTbl.qid_subst subst) (qi [ "F"; "P"; "T" ]))
          (qi [ "Arg"; "T" ])));
  let generic_imports = import [ "F" ] tbl in
  assert (List.length (SymbolTbl.find_import_targets (qi [ "f" ]) generic_imports) = 2);
  let tbl =
    tbl
    |> register (instance "Alias" [ "Instance" ])
    |> register (instance ~args:[ Module.ModArg (qi [ "Arg" ]) ] "Other" [ "F" ])
    |> register (module_ "Use" [])
  in
  List.iteri
    [ [ "Instance"; "Alias" ]; [ "Alias"; "Instance" ] ]
    ~f:(fun index order ->
      let name = "Use" ^ Int.to_string index in
      let scoped = register (module_ name []) tbl |> SymbolTbl.enter_exn (id name) in
      let scoped =
        List.fold order ~init:scoped ~f:(fun scoped name -> import [ name ] scoped)
      in
      assert (List.length (candidates [ "f" ] scoped) = 2);
      assert (List.length (SymbolTbl.find_import_targets (qi [ "f" ]) scoped) = 2);
      let scoped = import [ "Other" ] scoped in
      assert (List.length (candidates [ "f" ] scoped) = 4);
      assert (List.length (SymbolTbl.find_import_targets (qi [ "f" ]) scoped) = 4))

let test_sealed_exposure () =
  let interface_decl = { Module.empty_decl with mod_decl_is_interface = true } in
  let sealed_decl =
    {
      Module.empty_decl with
      mod_decl_is_sealed = true;
      mod_decl_returns = [ (qi [ "Public" ], []) ];
    }
  in
  let tbl =
    SymbolTbl.create ()
    |> register
         (module_ ~decl:interface_decl "Public"
            [ func "$visible1" "f"; func "$visible2" "f" ])
    |> register
         (module_ ~decl:sealed_decl "Implementation"
            [ func "$visible1" "f"; func "$visible2" "f"; func "$hidden" "hidden" ])
    |> register (instance "Sealed" [ "Implementation" ])
  in
  expect_targets [ "Sealed"; "f" ]
    [ [ "Sealed"; "$visible1" ]; [ "Sealed"; "$visible2" ] ]
    tbl;
  expect_targets [ "Sealed"; "hidden" ] [] tbl;
  let tbl = import [ "Sealed" ] tbl in
  expect_targets [ "f" ] [ [ "Sealed"; "$visible1" ]; [ "Sealed"; "$visible2" ] ] tbl;
  expect_targets [ "hidden" ] [] tbl

let test_sealed_instance_exposure () =
  let interface_decl = { Module.empty_decl with mod_decl_is_interface = true } in
  let implementation_decl =
    { Module.empty_decl with mod_decl_returns = [ (qi [ "Public" ], []) ] }
  in
  let tbl =
    SymbolTbl.create ()
    |> register
         (module_ ~decl:interface_decl "Public"
            [ func "$visible1" "f"; func "$visible2" "f" ])
    |> register
         (module_ ~decl:implementation_decl "Implementation"
            [ func "$visible1" "f"; func "$visible2" "f"; func "$hidden" "hidden" ])
    |> register (instance ~sealed:true ~typ:[ "Public" ] "Sealed" [ "Implementation" ])
  in
  expect_targets [ "Sealed"; "f" ]
    [ [ "Sealed"; "$visible1" ]; [ "Sealed"; "$visible2" ] ]
    tbl;
  expect_targets [ "Sealed"; "hidden" ] [] tbl

let test_cached_candidates () =
  let tbl = base () |> SymbolTbl.enter_exn (id "A") in
  expect_targets [ "f" ] [ [ "A"; "$a1" ]; [ "A"; "$a2" ] ] tbl;
  let _, cached = Hashtbl.find_exn tbl.tbl_curr.scope_cache (qi [ "f" ]) in
  let targets = List.map cached ~f:(fun (_, target, _) -> target) in
  assert (List.equal QualIdent.equal targets [ qi [ "A"; "$a1" ]; qi [ "A"; "$a2" ] ]);
  let position = { Lexing.dummy_pos with pos_lnum = 7; pos_cnum = 12 } in
  let loc = Util.Loc.make position position in
  let name = QualIdent.set_loc loc (qi [ "f" ]) in
  let resolved = SymbolTbl.resolve_and_find_candidates name tbl in
  List.iter resolved ~f:(fun (_, target, _, _) ->
      assert (Util.Loc.equal (QualIdent.to_loc target) loc))

let preserving_cache (f : SymbolTbl.t -> SymbolTbl.t) tbl =
  let generation = !(tbl.SymbolTbl.tbl_generation) in
  let tbl = f tbl in
  assert (Int.equal generation !(tbl.tbl_generation));
  tbl

let test_unchanged_bindings () =
  let tbl =
    base ()
    |> register (instance "AliasB" [ "B" ])
    |> SymbolTbl.enter_exn (id "Use")
    |> import [ "B" ]
  in
  expect_targets [ "f" ] [ [ "B"; "$b" ] ] tbl;
  let tbl =
    tbl
    |> preserving_cache (import [ "B" ])
    |> preserving_cache (import ~all:false [ "B"; "f" ])
    |> preserving_cache (import [ "AliasB" ])
    |> register (func "$local" "f")
  in
  expect_targets [ "f" ] [ [ "Use"; "$local" ] ] tbl;
  let tbl = preserving_cache (import [ "A" ]) tbl in
  expect_targets [ "f" ] [ [ "Use"; "$local" ] ] tbl;
  let tbl = preserving_cache (SymbolTbl.add_local_vars ~diagnostics []) tbl in
  let variable = Type.mk_var_decl (id "x") Type.int in
  let tbl = SymbolTbl.add_local_vars ~diagnostics [ variable ] tbl in
  assert (Option.is_some (SymbolTbl.resolve_and_find (qi [ "x" ]) tbl));
  let variable = { variable with var_type = Type.bool } in
  let tbl = preserving_cache (SymbolTbl.add_local_vars ~diagnostics [ variable ]) tbl in
  let () =
    match SymbolTbl.resolve_and_find (qi [ "x" ]) tbl with
    | Some (_, _, Module.VarDef { var_decl; _ }, _) ->
        assert (Type.equal var_decl.var_type Type.bool)
    | _ -> assert false
  in
  let tbl = SymbolTbl.add_transparent (id "alias") (qi [ "B"; "f" ]) tbl in
  expect_targets [ "alias" ] [ [ "B"; "$b" ] ] tbl;
  let tbl =
    preserving_cache (SymbolTbl.add_transparent (id "alias") (qi [ "B"; "f" ])) tbl
  in
  let tbl = SymbolTbl.add_transparent (id "alias") (qi [ "A"; "f" ]) tbl in
  expect_targets [ "alias" ] [ [ "A"; "$a1" ]; [ "A"; "$a2" ] ] tbl

let enter_callable module_name callable_name tbl =
  tbl |> SymbolTbl.enter_exn (id module_name) |> SymbolTbl.enter_exn (id callable_name)

let add_variable name tbl =
  register
    (Module.VarDef
       {
         var_decl = Type.mk_var_decl name Type.int;
         var_init = None;
         var_is_free = NotFree;
       })
    tbl

let invalidating_cache (f : SymbolTbl.t -> SymbolTbl.t) tbl =
  let generation = !(tbl.SymbolTbl.tbl_generation) in
  let tbl = f tbl in
  assert (Int.equal (generation + 1) !(tbl.tbl_generation));
  tbl

let expect_variable name declared tbl =
  match SymbolTbl.resolve_and_find (qi name) tbl with
  | Some (actual, _, Module.VarDef _, _) -> assert (QualIdent.equal actual (qi declared))
  | _ -> assert false

let test_local_name_filter () =
  let tbl = base () |> enter_callable "B" "$b" in
  expect_targets [ "f" ] [ [ "B"; "$b" ] ] tbl;
  let tbl =
    preserving_cache
      (SymbolTbl.add_local_vars ~diagnostics [ Type.mk_var_decl (id "x") Type.int ])
      tbl
  in
  expect_targets [ "f" ] [ [ "B"; "$b" ] ] tbl;
  expect_variable [ "x" ] [ "B"; "$b"; "x" ] tbl;
  let distinct = Ident.make Util.Loc.dummy "f" 1 in
  let tbl = preserving_cache (add_variable distinct) tbl in
  expect_targets [ "f" ] [ [ "B"; "$b" ] ] tbl;
  assert (Option.is_some (SymbolTbl.resolve_and_find (QualIdent.from_ident distinct) tbl));
  let tbl = invalidating_cache (add_variable (id "f")) tbl in
  expect_variable [ "f" ] [ "B"; "$b"; "f" ] tbl

let test_qualified_local_reads () =
  let tbl = base () |> enter_callable "B" "$b" |> import ~all:false [ "A" ] in
  expect_targets [ "B"; "$b"; "A"; "f" ] [ [ "A"; "$a1" ]; [ "A"; "$a2" ] ] tbl;
  let tbl = invalidating_cache (add_variable (id "A")) tbl in
  expect_targets [ "B"; "$b"; "A"; "f" ] [] tbl;
  expect_variable [ "B"; "$b"; "A" ] [ "B"; "$b"; "A" ] tbl

let test_reused_local_names () =
  let root = base () in
  let first = enter_callable "A" "$a1" root in
  expect_targets [ "f" ] [ [ "A"; "$a1" ]; [ "A"; "$a2" ] ] first;
  let second = enter_callable "B" "$b" root in
  let second = invalidating_cache (add_variable (id "f")) second in
  expect_variable [ "f" ] [ "B"; "$b"; "f" ] second;
  expect_targets [ "f" ] [ [ "A"; "$a1" ]; [ "A"; "$a2" ] ] first;
  let second = preserving_cache (add_variable (id "x")) second in
  let root = SymbolTbl.reset second in
  expect_variable [ "B"; "$b"; "x" ] [ "B"; "$b"; "x" ] root;
  let first = enter_callable "A" "$a1" root in
  let first = invalidating_cache (add_variable (id "x")) first in
  expect_variable [ "x" ] [ "A"; "$a1"; "x" ] first;
  expect_variable [ "B"; "$b"; "x" ] [ "B"; "$b"; "x" ] first

let test_local_read_generations () =
  let tbl = base () |> enter_callable "B" "$b" in
  expect_targets [ "f" ] [ [ "B"; "$b" ] ] tbl;
  let tbl =
    invalidating_cache (SymbolTbl.add_transparent (id "alias") (qi [ "A" ])) tbl
  in
  let tbl = preserving_cache (add_variable (id "f")) tbl in
  expect_variable [ "f" ] [ "B"; "$b"; "f" ] tbl;
  let tbl = base () |> enter_callable "B" "$b" in
  assert (
    Option.is_some (SymbolTbl.resolve_candidates ~canonical_aliases:true (qi [ "f" ]) tbl));
  let tbl = preserving_cache (add_variable (id "f")) tbl in
  expect_variable [ "f" ] [ "B"; "$b"; "f" ] tbl

let test_read_only_lookup () =
  let tbl = base () |> enter_callable "B" "$b" in
  let before = Hashtbl.length tbl.tbl_local_reads in
  let cache_size = Hashtbl.length tbl.tbl_curr.scope_cache in
  assert (Option.is_some (SymbolTbl.resolve_candidates ~read_only:true (qi [ "f" ]) tbl));
  assert (Hashtbl.length tbl.tbl_local_reads = before);
  assert (Hashtbl.length tbl.tbl_curr.scope_cache = cache_size);
  let tbl = preserving_cache (add_variable (id "f")) tbl in
  expect_variable [ "f" ] [ "B"; "$b"; "f" ] tbl

let () =
  test_read_only_lookup ();
  test_local_name_filter ();
  test_qualified_local_reads ();
  test_reused_local_names ();
  test_local_read_generations ();
  test_cached_candidates ();
  test_unchanged_bindings ();
  test_internal_scopes ();
  test_imports ();
  test_hiding_and_cache ();
  test_symbol_replacement ();
  test_aliases ();
  test_parameter_substitution ();
  test_sealed_exposure ();
  test_sealed_instance_exposure ()
