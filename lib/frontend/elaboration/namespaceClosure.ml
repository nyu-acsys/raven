open Base
open Ast
open Util

module Requirements = struct
  let union = AtomicityAnalysis.union_separation

  let equal left right =
    List.equal
      (fun left right -> AtomicityAnalysis.compare_separation left right = 0)
      left right
end

type collected = {
  program : Module.t;
  draft : NamespaceInference.t;
  analyses : AtomicityAnalysis.namespace_analysis Map.M(QualIdent).t;
}

let merge_imported_namespace (previous : NamespaceContract.namespace_decl)
    (incoming : NamespaceContract.namespace_decl) =
  let open NamespaceContract in
  let pairs =
    match List.zip incoming.formals previous.formals with
    | Ok pairs -> pairs
    | Unequal_lengths ->
        Error.internal_error
          (QualIdent.to_loc incoming.name)
          "Imported namespace declarations have different formal arities"
  in
  let renaming =
    List.fold pairs
      ~init:(Map.empty (module QualIdent))
      ~f:(fun renaming (source, target) ->
        Map.set renaming
          ~key:(QualIdent.from_ident source.Type.var_name)
          ~data:(Expr.from_var_decl target))
  in
  let align body =
    List.map body ~f:(fun (head, args) ->
        (head, List.map args ~f:(fun arg -> Expr.alpha_renaming arg renaming)))
  in
  let definition =
    match (previous.definition, incoming.definition) with
    | Abstract, Abstract -> Abstract
    | Defined body, Abstract -> Defined body
    | Abstract, Defined body -> Defined (align body)
    | Defined left, Defined right -> Defined (Callable.mask_union left (align right))
  in
  { previous with definition }

(* Imported summaries are read from headers, never reconstructed from lowered bodies. *)
let imported_summaries () =
  let open Rewriter.Syntax in
  let+ table = Rewriter.get_table in
  let rec gather owner contract (namespaces, callables) =
    match contract with
    | NamespaceContract.Module summary ->
        let namespaces =
          List.fold summary.namespaces ~init:namespaces ~f:(fun namespaces declaration ->
              Map.update namespaces declaration.NamespaceContract.name ~f:(function
                | None -> declaration
                | Some previous -> merge_imported_namespace previous declaration))
        in
        let callables =
          List.fold summary.callables ~init:callables ~f:(fun callables (name, summary) ->
              Map.set callables ~key:(QualIdent.append owner name) ~data:summary)
        in
        List.fold summary.modules ~init:(namespaces, callables)
          ~f:(fun state (name, contract) ->
            gather (QualIdent.append owner name) contract state)
    | Functor summary ->
        let state = gather owner summary.result (namespaces, callables) in
        List.fold summary.parameters ~init:state ~f:(fun state (name, contract) ->
            gather (QualIdent.append owner name) contract state)
  in
  Map.fold table.tbl_symbols
    ~init:(Map.empty (module QualIdent), Map.empty (module QualIdent))
    ~f:(fun ~key:owner ~data state ->
      match data with
      | Module.ModDef { mod_decl = { mod_decl_mask_contract = Some contract; _ }; _ }
        when QualIdent.is_local owner ->
          gather owner contract state
      | _ -> state)

let collect program =
  let open Rewriter.Syntax in
  let* namespaces, callables = imported_summaries () in
  let* draft =
    NamespaceInference.infer ~namespaces:(Map.data namespaces)
      ~callables:(Map.to_alist callables) program
  in
  let collect_callable call =
    match call.Callable.call_def with
    | FuncDef _ | ProcDef { proc_body = None } -> Rewriter.return call
    | ProcDef { proc_body = Some _ } ->
        let* name = Rewriter.current_scope_id in
        let* analysis = AtomicityAnalysis.collect_namespace_requirements draft call in
        let* analyses = Rewriter.current_user_state in
        let analyses =
          match Map.add analyses ~key:name ~data:analysis with
          | `Ok analyses -> analyses
          | `Duplicate ->
              Error.internal_error call.call_decl.call_decl_loc
                "A callable was analyzed twice for namespace requirements"
        in
        let+ () = Rewriter.set_user_state analyses in
        analysis.callable
  in
  Rewriter.eval_with_user_state
    ~init:(Map.empty (module QualIdent))
    (let* program = Rewriter.Module.rewrite_callables ~f:collect_callable program in
     let+ analyses = Rewriter.current_user_state in
     { program; draft; analyses })

(** Close only summary edges; the transformed bodies are retained unchanged. *)
let close collected =
  let open Rewriter.Syntax in
  let initial =
    Map.fold collected.analyses ~init:collected.draft.callables
      ~f:(fun ~key:name ~data:analysis callables ->
        Map.update callables name ~f:(fun summary ->
            {
              (Option.value_exn summary) with
              NamespaceContract.separation = analysis.AtomicityAnalysis.separation;
            }))
  in
  let rec fixed_point callables =
    let draft = { collected.draft with NamespaceInference.callables } in
    let* next =
      Rewriter.List.fold_left (Map.to_alist collected.analyses) ~init:callables
        ~f:(fun summaries (name, analysis) ->
          let* inherited =
            Rewriter.in_scope_of name
              (Rewriter.List.map (Set.to_list analysis.AtomicityAnalysis.callees)
                 ~f:(fun callee ->
                   let+ summary = NamespaceInference.find_callable draft callee in
                   match summary with
                   | Some summary -> summary.NamespaceContract.separation
                   | None ->
                       Error.internal_error (QualIdent.to_loc callee)
                         "Missing callee namespace summary during requirement closure"))
          in
          let separation =
            List.fold inherited ~init:analysis.separation ~f:Requirements.union
          in
          Rewriter.return
            (Map.update summaries name ~f:(fun previous ->
                 { (Option.value_exn previous) with NamespaceContract.separation })))
    in
    if
      Map.for_alli callables ~f:(fun ~key ~data:previous ->
          Requirements.equal previous.NamespaceContract.separation
            (Map.find_exn next key).NamespaceContract.separation)
    then Rewriter.return { draft with callables = next }
    else fixed_point next
  in
  fixed_point initial

let requirements = function
  | NamespaceContract.Module summary -> summary.separation
  | Functor summary -> summary.separation

let add_requirements separation = function
  | NamespaceContract.Module summary ->
      NamespaceContract.Module
        { summary with separation = Requirements.union separation summary.separation }
  | Functor summary ->
      Functor
        { summary with separation = Requirements.union separation summary.separation }

(** Reify a header, consuming only parameters bound by this application. *)
let reify_module_contract ?(retain_parameter_members = true)
    ((original, symbol, substitution) as resolved) contract =
  let open Rewriter.Syntax in
  match symbol with
  | Module.ModDef m ->
      let+ rewritten =
        Rewriter.NamespaceContract.rewrite_qual_idents
          ~f:(QualIdent.requalify (Rewriter.Symbol.subst resolved))
          contract
      in
      begin match rewritten with
      | NamespaceContract.Module _ -> rewritten
      | Functor summary ->
          let result =
            if retain_parameter_members then summary.result
            else
              match summary.result with
              | NamespaceContract.Module result ->
                  Module
                    {
                      result with
                      modules =
                        List.filter result.modules ~f:(fun (name, _) ->
                            not
                              (List.Assoc.mem summary.parameters name ~equal:Ident.equal));
                    }
              | Functor _ as result -> result
          in
          let parameters =
            List.filter summary.parameters ~f:(fun (parameter, _) ->
                not
                  (SymbolTbl.has_binding
                     (QualIdent.append original parameter)
                     substitution))
          in
          let consumed =
            match m.mod_decl.mod_decl_parameters with
            | Structure -> false
            | UnitParameter ->
                SymbolTbl.module_is_instantiated original m.mod_decl substitution
            | NamedParameters _ -> List.is_empty parameters
          in
          if consumed then add_requirements summary.separation result
          else Functor { summary with parameters; result }
      end
  | _ ->
      Error.internal_error (QualIdent.to_loc original)
        "Expected a module namespace contract"

let declared_contract name symbol =
  match symbol with
  | Module.ModDef { mod_decl = { mod_decl_mask_contract = Some contract; _ }; _ } ->
      contract
  | _ ->
      Error.internal_error (QualIdent.to_loc name)
        "A module namespace contract is needed before it has been frozen"

let find_module_contract ?(retain_parameter_members = true) name =
  let open Rewriter.Syntax in
  let* _, resolved = Rewriter.resolve_and_find name in
  reify_module_contract ~retain_parameter_members resolved
    (declared_contract name (Rewriter.Symbol.orig_symbol resolved))

type freezing = Building | Frozen of Module.t

let freeze ?(refresh = false) ?(requirements = Map.empty (module QualIdent)) draft program
    =
  let open Rewriter.Syntax in
  let root = QualIdent.from_ident program.Module.mod_decl.mod_decl_name in
  let rec index name m modules =
    if (not refresh) && Option.is_some m.Module.mod_decl.mod_decl_mask_contract then
      Error.internal_error m.mod_decl.mod_decl_loc
        "A module namespace contract was frozen twice";
    List.fold m.mod_def ~init:(Map.set modules ~key:name ~data:m)
      ~f:(fun modules -> function
      | Module.SymbolDef (ModDef child) ->
          index (QualIdent.append name child.mod_decl.mod_decl_name) child modules
      | _ -> modules)
  in
  let sources = index root program (Map.empty (module QualIdent)) in
  (* Only metadata needs a module scope; no body or local scope is entered here. *)
  let in_module name action =
    Rewriter.in_scope_of (Module.unit_parameter_path name) action
  in
  let rec lookup name =
    let* _, resolved = Rewriter.resolve_and_find name in
    let original = Rewriter.Symbol.orig_qid resolved in
    let* contract =
      if Map.mem sources original then
        let+ m = build original in
        Option.value_exn m.Module.mod_decl.mod_decl_mask_contract
      else Rewriter.return (declared_contract name (Rewriter.Symbol.orig_symbol resolved))
    in
    reify_module_contract resolved contract
  and build owner =
    let* cache = Rewriter.current_user_state in
    match Map.find cache owner with
    | Some (Frozen m) -> Rewriter.return m
    | Some Building ->
        Error.type_error (QualIdent.to_loc owner)
          "Cyclic module namespace contract dependency"
    | None ->
        let m = Map.find_exn sources owner in
        let* () = Rewriter.set_user_state (Map.set cache ~key:owner ~data:Building) in
        let* frozen = in_module owner (build_contents owner m) in
        let* () =
          Rewriter.in_scope_of owner (Rewriter.set_symbol (Module.ModDef frozen))
        in
        let* cache = Rewriter.current_user_state in
        let+ () =
          Rewriter.set_user_state (Map.set cache ~key:owner ~data:(Frozen frozen))
        in
        frozen
  and build_contents owner m =
    let* parameters =
      Rewriter.List.map (Module.formals m.Module.mod_decl) ~f:(fun parameter ->
          let+ contract = lookup (QualIdent.from_ident parameter.mod_inst_name) in
          (parameter.mod_inst_name, contract))
    in
    let* definitions =
      Rewriter.List.map m.mod_def ~f:(function
        | Module.SymbolDef (ModDef child) ->
            let+ child = build (QualIdent.append owner child.mod_decl.mod_decl_name) in
            Module.SymbolDef (ModDef child)
        | definition -> Rewriter.return definition)
    in
    let* namespaces, callables, modules =
      Rewriter.List.fold_left definitions ~init:([], [], [])
        ~f:(fun (namespaces, callables, modules) definition ->
          match definition with
          | Module.SymbolDef (CallDef call) ->
              let name = QualIdent.append owner call.call_decl.call_decl_name in
              let* summary = NamespaceInference.find_callable draft name in
              let summary =
                match summary with
                | Some summary -> summary
                | None ->
                    Error.internal_error call.call_decl.call_decl_loc
                      "Missing callable namespace summary while freezing"
              in
              let namespaces =
                match Map.find draft.NamespaceInference.namespaces name with
                | None -> namespaces
                | Some declaration -> declaration :: namespaces
              in
              Rewriter.return
                ( namespaces,
                  (call.call_decl.call_decl_name, summary) :: callables,
                  modules )
          | Module.SymbolDef (ModDef child) ->
              let contract = Option.value_exn child.mod_decl.mod_decl_mask_contract in
              Rewriter.return
                ( namespaces,
                  callables,
                  (child.mod_decl.mod_decl_name, contract) :: modules )
          | Module.SymbolDef (ModInst instance) ->
              let+ contract = lookup (QualIdent.from_ident instance.mod_inst_name) in
              (namespaces, callables, (instance.mod_inst_name, contract) :: modules)
          | SymbolDef (TypeDef _ | FieldDef _ | VarDef _ | ConstrDef _ | DestrDef _)
          | Import _ ->
              Rewriter.return (namespaces, callables, modules))
    in
    let separation =
      List.fold callables ~init:[] ~f:(fun separation (_, summary) ->
          Requirements.union separation summary.NamespaceContract.separation)
    in
    let separation =
      List.fold modules ~init:separation ~f:(fun separation (name, contract) ->
          let interface =
            List.exists definitions ~f:(function
              | Module.SymbolDef (ModDef child) ->
                  Ident.equal name child.mod_decl.mod_decl_name
                  && child.mod_decl.mod_decl_is_interface
              | _ -> false)
          in
          match contract with
          | NamespaceContract.Module summary when not interface ->
              Requirements.union separation summary.separation
          | Module _ | Functor _ -> separation)
    in
    let separation =
      Requirements.union separation
        (Option.value (Map.find requirements owner) ~default:[])
    in
    let definitions =
      List.map definitions ~f:(function
        | Module.SymbolDef (CallDef call) ->
            let summary =
              List.Assoc.find_exn callables call.call_decl.call_decl_name
                ~equal:Ident.equal
            in
            Module.SymbolDef
              (CallDef
                 {
                   call with
                   call_decl =
                     {
                       call.call_decl with
                       call_decl_needs_mask = Some summary.requires;
                       call_decl_grants_mask = Some summary.grants;
                     };
                 })
        | definition -> definition)
    in
    let modules = List.rev modules in
    let parameter_members =
      List.filter parameters ~f:(fun (name, _) ->
          not (List.Assoc.mem modules name ~equal:Ident.equal))
    in
    let result =
      NamespaceContract.Module
        {
          namespaces = List.rev namespaces;
          callables = List.rev callables;
          modules = parameter_members @ modules;
          separation;
        }
    in
    let contract =
      match m.mod_decl.mod_decl_parameters with
      | Structure -> result
      | NamedParameters _ | UnitParameter ->
          NamespaceContract.Functor { parameters; separation; result }
    in
    Rewriter.return
      {
        Module.mod_def = definitions;
        mod_decl = { m.mod_decl with mod_decl_mask_contract = Some contract };
      }
  in
  Rewriter.eval_with_user_state ~init:(Map.empty (module QualIdent)) (build root)

(** Conditional frozen contracts; realization validation is a separate phase. *)
let elaborate program =
  let open Rewriter.Syntax in
  let* collected = collect program in
  let* draft = close collected in
  freeze draft collected.program
