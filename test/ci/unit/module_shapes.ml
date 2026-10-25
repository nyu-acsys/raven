open Base
open Raven
open Ast

let loc = Util.Loc.dummy
let id name = Ident.make loc name 0
let qi names = QualIdent.from_list (List.map names ~f:id)
let formal name = Module.mk_mod_inst ~name:(id name) ~typ:(qi [ "Interface" ]) ~loc ()
let declaration parameters = { Module.empty_decl with mod_decl_parameters = parameters }

let test_parameter_shapes () =
  let structure = declaration Module.Structure in
  let factory = declaration Module.UnitParameter in
  let named = declaration (Module.parameters_of_formals [ formal "Element" ]) in
  assert (Module.is_structure structure);
  assert (not (Module.is_functor structure));
  assert (Module.is_functor named);
  assert (Module.is_named_functor named);
  assert (Module.is_functor factory);
  assert (not (Module.is_structure factory));
  assert (not (Module.is_named_functor factory));
  assert (List.is_empty (Module.formals structure));
  assert (List.is_empty (Module.formals factory));
  assert (
    List.equal Ident.equal
      (List.map (Module.formals named) ~f:(fun parameter -> parameter.mod_inst_name))
      [ id "Element" ]);
  match Module.parameters_of_formals [] with
  | Structure -> ()
  | NamedParameters _ | UnitParameter -> assert false

let test_legacy_bindings () =
  let target = qi [ "Target" ] in
  let make ?def () = Module.mk_mod_inst ~name:(id "Binding") ~typ:target ?def ~loc () in
  assert (Option.is_none (make ()).mod_inst_def);
  begin match (make ~def:(target, []) ()).mod_inst_def with
  | Some (Alias actual) -> assert (QualIdent.equal target actual)
  | None | Some (Apply _ | ApplyUnit _) -> assert false
  end;
  match (make ~def:(target, [ Module.ModArg (qi [ "Argument" ]) ]) ()).mod_inst_def with
  | Some (Apply (actual, [ ModArg argument ])) ->
      assert (QualIdent.equal target actual);
      assert (QualIdent.equal argument (qi [ "Argument" ]))
  | None | Some (Alias _ | ApplyUnit _ | Apply _) -> assert false

let test_application_rewriting () =
  let original = qi [ "Original" ] and rewritten = qi [ "Rewritten" ] in
  let argument = Module.ModArg (qi [ "Argument" ]) in
  let target _ = rewritten in
  let no_arguments _ = assert false in
  let alias = Module.map_application (Alias original) ~target ~args:no_arguments in
  let factory = Module.map_application (ApplyUnit original) ~target ~args:no_arguments in
  begin match (alias, factory) with
  | Alias alias_target, ApplyUnit factory_target ->
      assert (QualIdent.equal alias_target rewritten);
      assert (QualIdent.equal factory_target rewritten)
  | _ -> assert false
  end;
  let application =
    Module.map_application
      (Apply (original, [ argument ]))
      ~target
      ~args:(fun _ -> [ Module.TypeArg Type.int ])
  in
  begin match application with
  | Apply (actual, [ TypeArg typ ]) ->
      assert (QualIdent.equal actual rewritten);
      assert (Type.equal typ Type.int)
  | Alias _ | ApplyUnit _ | Apply _ -> assert false
  end;
  List.iter [ alias; factory; application ] ~f:(fun application ->
      assert (QualIdent.equal (Module.application_target application) rewritten));
  assert (List.is_empty (Module.application_args alias));
  assert (List.is_empty (Module.application_args factory));
  assert (List.length (Module.application_args application) = 1)

let substitution rules = (true, false, rules)
let binding source target = (qi source, QualIdent.to_list (qi target))

let test_own_instantiation () =
  let outer = binding [ "Outer" ] [ "Instance" ] in
  let fresh = qi [ "Outer"; "Fresh" ] in
  let factory = declaration Module.UnitParameter in
  let applied rules =
    SymbolTbl.module_is_instantiated fresh factory (substitution rules)
  in
  assert (not (applied []));
  assert (not (applied [ outer ]));
  assert (not (applied [ outer; binding [ "Instance"; "Sibling" ] [ "Other" ] ]));
  assert (not (applied [ binding [ "Outer"; "Fresh" ] [ "Alias" ] ]));
  assert (not (applied [ outer; binding [ "Instance"; "Fresh" ] [ "Formal" ] ]));
  let consume path =
    (Module.unit_parameter_path (qi path), QualIdent.to_list (qi [ "Created" ]))
  in
  assert (applied [ consume [ "Outer"; "Fresh" ] ]);
  assert (applied [ outer; consume [ "Instance"; "Fresh" ] ]);
  let named = declaration (Module.NamedParameters [ formal "First"; formal "Second" ]) in
  let applied rules = SymbolTbl.module_is_instantiated fresh named (substitution rules) in
  let first = binding [ "Instance"; "Fresh"; "First" ] [ "FirstArgument" ] in
  let second = binding [ "Instance"; "Fresh"; "Second" ] [ "SecondArgument" ] in
  assert (not (applied [ outer ]));
  assert (not (applied [ outer; first ]));
  assert (applied [ outer; first; second ]);
  let structure = declaration Module.Structure in
  assert (not (SymbolTbl.module_is_instantiated fresh structure (substitution [ outer ])));
  assert (
    SymbolTbl.module_is_instantiated fresh structure
      (substitution [ outer; binding [ "Instance"; "Fresh" ] [ "Created" ] ]))

let test_factory_aliases () =
  let diagnostics = Util.Diagnostics.create () in
  let factory name ~interface =
    Module.ModDef
      {
        mod_decl =
          {
            Module.empty_decl with
            mod_decl_name = id name;
            mod_decl_parameters = UnitParameter;
            mod_decl_is_interface = interface;
          };
        mod_def = [];
      }
  in
  let register symbol table = SymbolTbl.add_symbol ~diagnostics symbol table in
  let table =
    SymbolTbl.create ()
    |> register (factory "Fresh" ~interface:false)
    |> register (factory "Factory" ~interface:true)
    |> register
         (Module.ModInst
            (Module.mk_mod_inst ~name:(id "Alias") ~typ:(qi [ "Fresh" ])
               ~def:(qi [ "Fresh" ], [])
               ~loc ()))
    |> register
         (Module.ModInst
            (Module.mk_mod_inst ~name:(id "Formal") ~typ:(qi [ "Factory" ])
               ~is_interface:true ~loc ()))
  in
  List.iter [ "Alias"; "Formal" ] ~f:(fun name ->
      let owner, _, symbol, subst = SymbolTbl.resolve_and_find_exn (qi [ name ]) table in
      match symbol with
      | Module.ModDef module_ ->
          assert (not (SymbolTbl.module_is_instantiated owner module_.mod_decl subst));
          assert (Module.is_functor module_.mod_decl)
      | _ -> assert false)

let () =
  test_parameter_shapes ();
  test_legacy_bindings ();
  test_application_rewriting ();
  test_own_instantiation ();
  test_factory_aliases ()
