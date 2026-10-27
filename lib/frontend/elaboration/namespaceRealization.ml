open Base
open Ast
open Util
open NamespaceContract
module Entailment = NamespaceEntailment
module Requirements = NamespaceClosure.Requirements

type environment = {
  roots : QualIdentSet.t;
  universals : QualIdentSet.t;
  assumptions : NamespaceContract.separation_requirement list;
}

let empty_environment =
  {
    roots = Set.empty (module QualIdent);
    universals = Set.empty (module QualIdent);
    assumptions = [];
  }

let below root name =
  List.is_prefix (QualIdent.to_list name) ~prefix:(QualIdent.to_list root)
    ~equal:Ident.equal

let map_contract rename = Rewriter.NamespaceContract.rewrite_qual_idents ~f:rename

let result = function
  | NamespaceContract.Module _ as contract -> contract
  | Functor summary -> summary.result

let own_namespaces = function
  | NamespaceContract.Module summary -> summary.namespaces
  | Functor _ -> []

let requirements = NamespaceClosure.requirements

let report ~loc requirement =
  let show mask =
    String.concat ~sep:", "
      (List.map mask ~f:(fun (head, _) ->
           Stdlib.Format.asprintf "%a" Callable.pr_mask_head head))
  in
  Error.fail_with
    [
      ( Error.Type,
        loc,
        Printf.sprintf "Cannot establish invariant namespace separation between %s and %s"
          (show requirement.NamespaceContract.left)
          (show requirement.right) );
      ( Error.RelatedLoc,
        requirement.loc,
        "This generic check requires the namespaces to be disjoint" );
    ]

let overlaps ?(rename = Fn.id) context requirement =
  let open Rewriter.Syntax in
  let* left =
    Entailment.normalize_mask ~rename context requirement.NamespaceContract.left
  in
  let+ right = Entailment.normalize_mask ~rename context requirement.right in
  List.exists left ~f:(fun (head, _) ->
      match head with
      | Callable.MaskHead.Dependencies _ -> false
      | Invariant _ ->
          List.exists right ~f:(fun (other, _) -> Callable.equal_mask_head head other))

let remember ~owner constraints =
  let open Rewriter.Syntax in
  let* pending = Rewriter.current_user_state in
  Rewriter.set_user_state
    (Map.update pending owner ~f:(fun previous ->
         Requirements.union (Option.value previous ~default:[]) constraints))

let require ?(rename = Fn.id) ~context ~owner ~loc environment requirement =
  let open Rewriter.Syntax in
  let* satisfied =
    Entailment.entails ~rename context ~assumptions:environment.assumptions requirement
  in
  if satisfied then Rewriter.return ()
  else
    let* conflict = overlaps ~rename context requirement in
    if conflict then report ~loc requirement
    else
      let* left =
        Entailment.normalize_mask ~rename context requirement.NamespaceContract.left
      in
      let* right = Entailment.normalize_mask ~rename context requirement.right in
      let* bound =
        Entailment.mentions ~rename ~conservative:true ~roots:environment.universals
          (left @ right @ requirement.left @ requirement.right)
      in
      let* symbolic =
        Entailment.mentions ~rename ~roots:environment.roots
          (left @ right @ requirement.left @ requirement.right)
      in
      if bound || not symbolic then report ~loc requirement
      else
        let* left = Entailment.canonical_mask ~rename requirement.left in
        let* right = Entailment.canonical_mask ~rename requirement.right in
        let requirement = { requirement with left; right } in
        let* pending = Rewriter.current_user_state in
        Rewriter.set_user_state
          (Map.update pending owner ~f:(fun previous ->
               Requirements.union (Option.value previous ~default:[]) [ requirement ]))

let require_all ?(rename = Fn.id) ~context ~owner ~loc environment constraints =
  Rewriter.List.iter constraints ~f:(require ~rename ~context ~owner ~loc environment)

let align_callable (actual : NamespaceContract.callable_summary)
    (expected : NamespaceContract.callable_summary) =
  let pairs =
    match
      List.zip (expected.formals @ expected.returns) (actual.formals @ actual.returns)
    with
    | Ok pairs -> pairs
    | Unequal_lengths ->
        Error.internal_error Loc.dummy
          "Inconsistent callable binders in namespace contracts"
  in
  let renaming =
    List.fold pairs
      ~init:(Map.empty (module QualIdent))
      ~f:(fun renaming (source, target) ->
        Map.set renaming
          ~key:(QualIdent.from_ident source.Type.var_name)
          ~data:(Expr.from_var_decl target))
  in
  NamespaceContract.map_callable_summary ~name:Fn.id
    ~expr:(fun expression -> Expr.alpha_renaming expression renaming)
    ~typ:Fn.id expected

let grants_cover ?(rename = Fn.id) context ~assumptions provided promised =
  let open Rewriter.Syntax in
  let check assumptions required =
    let* available = Entailment.available_grants ~rename context ~assumptions provided in
    let* available = Entailment.canonical_mask ~rename available in
    let+ required = Entailment.canonical_mask ~rename required in
    Entailment.covered ~by:available required
  in
  let* unconditional = check assumptions promised.NamespaceContract.grants in
  if not unconditional then Rewriter.return false
  else
    Rewriter.List.for_all promised.guarded_grants ~f:(fun grant ->
        let* impossible =
          Entailment.impossible_conditions ~rename context grant.conditions
        in
        if impossible then Rewriter.return true
        else check (Requirements.union assumptions grant.conditions) grant.grants)

let matching_callable actual name kind =
  let candidates =
    List.filter actual ~f:(fun (candidate, provided) ->
        String.equal (Ident.name candidate) (Ident.name name)
        && Poly.(provided.NamespaceContract.kind = kind))
  in
  match candidates with [ (_, provided) ] -> Some provided | _ -> None

let signature_error loc message =
  Error.type_error loc ("Incompatible module namespace contracts: " ^ message)

let effective_path ?(implementation = true) name =
  let open Rewriter.Syntax in
  let+ table = Rewriter.get_table in
  match
    SymbolTbl.resolve_and_find ~implementation ~read_only:true name
      (SymbolTbl.goto name table)
  with
  | None -> name
  | Some (original, _, _, substitution) ->
      QualIdent.requalify (SymbolTbl.qid_subst substitution) original

(** Structural shape/type compliance has already been checked by the nominal checker. *)
let rec compatible ~declarations ~owner ~loc environment ~actual_path ~expected_path
    ?(rename = Fn.id) ~established actual expected =
  let open Rewriter.Syntax in
  let* actual_path = effective_path actual_path in
  match (actual, expected) with
  | NamespaceContract.Module actual, Module expected ->
      let owner_rename name =
        rename
          (QualIdent.requalify [ (expected_path, QualIdent.to_list actual_path) ] name)
      in
      let* expected = map_contract owner_rename (NamespaceContract.Module expected) in
      let expected =
        match expected with Module summary -> summary | Functor _ -> assert false
      in
      let* context = Entailment.create ~rename (declarations @ actual.namespaces) in
      let overrides =
        List.filter expected.namespaces ~f:(fun declaration ->
            match declaration.NamespaceContract.definition with
            | Defined _ -> true
            | Abstract -> false)
      in
      let* budget = Entailment.create ~rename ~overrides (Map.data context.namespaces) in
      let environment =
        if established then
          {
            environment with
            assumptions = Requirements.union environment.assumptions actual.separation;
          }
        else environment
      in
      let* () =
        require_all ~rename ~context ~owner ~loc environment expected.separation
      in
      let environment =
        {
          environment with
          assumptions = Requirements.union environment.assumptions expected.separation;
        }
      in
      let* () =
        Rewriter.List.iter expected.callables ~f:(fun (name, promised) ->
            (* Functions have no namespace effects; nominal typing matches their overloads. *)
            match promised.NamespaceContract.kind with
            | Callable.Func -> Rewriter.return ()
            | Proc | Lemma | Pred | Invariant ->
                let provided = matching_callable actual.callables name promised.kind in
                begin match provided with
                | None -> signature_error loc "a callable summary is missing"
                | Some provided ->
                    let promised = align_callable provided promised in
                    let abstract_resource =
                      List.exists expected.namespaces ~f:(fun declaration ->
                          QualIdent.equal declaration.name
                            (QualIdent.append actual_path name)
                          &&
                          match declaration.definition with
                          | Abstract -> true
                          | Defined _ -> false)
                    in
                    let* required =
                      Entailment.normalize_mask ~rename context provided.requires
                    in
                    let* allowed =
                      Entailment.normalize_mask ~rename budget promised.requires
                    in
                    let* grants_ok =
                      grants_cover ~rename context ~assumptions:environment.assumptions
                        provided promised
                    in
                    if
                      (not abstract_resource)
                      && not (Entailment.covered ~by:allowed required)
                    then
                      signature_error loc
                        ("the required mask of " ^ Ident.to_string name
                       ^ " exceeds the promised mask")
                    else if not grants_ok then
                      signature_error loc
                        ("the granted mask of " ^ Ident.to_string name
                       ^ " is weaker than promised")
                    else
                      require_all ~rename ~context ~owner ~loc environment
                        provided.separation
                end)
      in
      Rewriter.List.iter expected.modules ~f:(fun (name, promised) ->
          match List.Assoc.find actual.modules name ~equal:Ident.equal with
          | None -> signature_error loc "a nested module summary is missing"
          | Some provided ->
              compatible ~declarations ~owner ~loc environment
                ~actual_path:(QualIdent.append actual_path name)
                ~expected_path:(QualIdent.append actual_path name)
                ~rename ~established:true provided promised)
  | Functor actual, Functor expected ->
      if List.length actual.parameters <> List.length expected.parameters then
        signature_error loc "functor parameter shapes differ";
      let pairs = List.zip_exn actual.parameters expected.parameters in
      let actual_parameter_roots =
        List.map pairs ~f:(fun ((actual, _), (expected, _)) ->
            ( QualIdent.append actual_path actual,
              QualIdent.to_list (QualIdent.append expected_path expected) ))
      in
      let actual_rename name = rename (QualIdent.requalify actual_parameter_roots name) in
      let expected_roots =
        List.map expected.parameters ~f:(fun (name, _) ->
            QualIdent.append expected_path name)
      in
      let expected_rename name =
        if List.exists expected_roots ~f:(fun root -> below root name) then rename name
        else
          rename
            (QualIdent.requalify [ (expected_path, QualIdent.to_list actual_path) ] name)
      in
      let* actual = map_contract actual_rename (NamespaceContract.Functor actual) in
      let* expected = map_contract expected_rename (NamespaceContract.Functor expected) in
      let actual =
        match actual with Functor summary -> summary | Module _ -> assert false
      in
      let expected =
        match expected with Functor summary -> summary | Module _ -> assert false
      in
      let* context =
        Entailment.create ~rename:actual_rename
          (declarations @ own_namespaces actual.result)
      in
      (* An impossible promised condition cannot justify a realization. *)
      let* () =
        Rewriter.List.iter expected.separation ~f:(fun requirement ->
            let+ conflict = overlaps ~rename:actual_rename context requirement in
            if conflict then report ~loc requirement)
      in
      let inputs =
        List.concat_map expected.parameters ~f:(fun (_, contract) ->
            match contract with Module summary -> summary.separation | Functor _ -> [])
      in
      let environment =
        {
          environment with
          universals = Set.add (Set.add environment.universals actual_path) expected_path;
          assumptions =
            Requirements.union environment.assumptions
              (Requirements.union inputs expected.separation);
        }
      in
      let* () =
        require_all ~rename:actual_rename ~context ~owner ~loc environment
          actual.separation
      in
      let* () =
        Rewriter.List.iter (List.zip_exn actual.parameters expected.parameters)
          ~f:(fun ((_, demanded), (parameter, supplied)) ->
            let path = QualIdent.append expected_path parameter in
            compatible ~declarations ~owner ~loc environment ~actual_path:path
              ~expected_path:path ~rename:actual_rename ~established:true supplied
              demanded)
      in
      let without_formal_members parameters = function
        | NamespaceContract.Module result ->
            Module
              {
                result with
                modules =
                  List.filter result.modules ~f:(fun (name, _) ->
                      not (List.Assoc.mem parameters name ~equal:Ident.equal));
              }
        | Functor _ as result -> result
      in
      compatible ~declarations ~owner ~loc environment ~actual_path
        ~expected_path:actual_path ~rename:actual_rename ~established:true
        (without_formal_members actual.parameters actual.result)
        (without_formal_members expected.parameters expected.result)
  | Module _, Functor _ | Functor _, Module _ ->
      signature_error loc "module/functor shapes differ"

let snapshot_contract ?(implementation = false) name =
  let open Rewriter.Syntax in
  if not implementation then
    NamespaceClosure.find_module_contract ~retain_parameter_members:false name
  else
    let* table = Rewriter.get_table in
    match
      SymbolTbl.resolve_and_find ~implementation:true ~read_only:true name
        (SymbolTbl.goto name table)
    with
    | None ->
        Error.internal_error (QualIdent.to_loc name)
          "Missing module implementation namespace contract"
    | Some (original, _, symbol, substitution) ->
        NamespaceClosure.reify_module_contract
          (original, symbol, substitution)
          (NamespaceClosure.declared_contract name symbol)

let validate_pass ~declarations program pending =
  let open Rewriter.Syntax in
  let* context = Entailment.create declarations in
  let rec walk environment owner (m : Module.t) =
    Rewriter.in_scope_of
      (Module.unit_parameter_path owner)
      (let* contract =
         Rewriter.NamespaceContract.rewrite_qual_idents
           ~f:(QualIdent.requalify m.mod_decl.mod_decl_instance_subst)
           (Option.value_exn m.Module.mod_decl.mod_decl_mask_contract)
       in
       let here =
         if m.mod_decl.mod_decl_is_interface || Module.is_functor m.mod_decl then
           { environment with roots = Set.add environment.roots owner }
         else environment
       in
       let* here =
         match contract with
         | NamespaceContract.Module _ -> Rewriter.return here
         | Functor summary ->
             let assumptions =
               List.concat_map summary.parameters ~f:(fun (_, parameter) ->
                   match parameter with
                   | Module summary -> summary.separation
                   | Functor _ -> [])
             in
             Rewriter.return
               {
                 here with
                 roots =
                   List.fold summary.parameters ~init:here.roots
                     ~f:(fun roots (name, _) ->
                       Set.add roots (QualIdent.append owner name));
                 assumptions = Requirements.union here.assumptions assumptions;
               }
       in
       let* () =
         require_all ~context ~owner ~loc:m.mod_decl.mod_decl_loc here
           (requirements contract)
       in
       let* () =
         Rewriter.List.iter m.mod_decl.mod_decl_returns ~f:(fun parent ->
             let* parent_symbol = Interfaces.realize_parent ~owner parent in
             let parent_contract =
               NamespaceClosure.declared_contract (fst parent)
                 (Rewriter.Symbol.orig_symbol parent_symbol)
             in
             let* promised =
               NamespaceClosure.reify_module_contract ~retain_parameter_members:false
                 parent_symbol parent_contract
             in
             let* promised =
               Rewriter.NamespaceContract.rewrite_qual_idents
                 ~f:(QualIdent.requalify m.mod_decl.mod_decl_instance_subst)
                 promised
             in
             let* () =
               require_all ~context ~owner ~loc:m.mod_decl.mod_decl_loc here
                 (requirements promised)
             in
             let* () = remember ~owner (requirements promised) in
             let comparison =
               if Module.is_functor m.mod_decl then
                 {
                   environment with
                   universals = Set.add environment.universals owner;
                   assumptions =
                     Requirements.union here.assumptions (requirements promised);
                 }
               else here
             in
             compatible ~declarations ~owner ~loc:m.mod_decl.mod_decl_loc comparison
               ~actual_path:owner ~expected_path:owner
               ~established:(not (Module.is_functor m.mod_decl))
               (result contract) (result promised))
       in
       Rewriter.List.iter m.mod_def ~f:(function
         | Module.SymbolDef (ModDef child) ->
             walk here (QualIdent.append owner child.mod_decl.mod_decl_name) child
         | SymbolDef (ModInst binding) -> application here owner binding
         | SymbolDef
             (CallDef _ | TypeDef _ | VarDef _ | FieldDef _ | ConstrDef _ | DestrDef _)
         | Import _ ->
             Rewriter.return ()))
  and application environment owner binding =
    let name = QualIdent.append owner binding.Module.mod_inst_name in
    match binding.mod_inst_def with
    | None -> Rewriter.return ()
    | Some definition ->
        let* table = Rewriter.get_table in
        let* () =
          match SymbolTbl.application_origin name table with
          | None -> Rewriter.return ()
          | Some (head, arguments) ->
              let* contract = snapshot_contract head in
              begin match contract with
              | Module _ -> Rewriter.return ()
              | Functor functor_ ->
                  let bindings =
                    List.map arguments ~f:(fun (formal, actual) ->
                        (QualIdent.append head formal, QualIdent.to_list actual))
                  in
                  Rewriter.List.iter arguments ~f:(fun (formal, actual_path) ->
                      match
                        List.Assoc.find functor_.parameters formal ~equal:Ident.equal
                      with
                      | None ->
                          signature_error binding.mod_inst_loc
                            "application parameter metadata is missing"
                      | Some promised ->
                          let* promised =
                            map_contract (QualIdent.requalify bindings) promised
                          in
                          let* provided =
                            snapshot_contract ~implementation:true actual_path
                          in
                          compatible ~declarations ~owner ~loc:binding.mod_inst_loc
                            environment ~actual_path ~expected_path:actual_path
                            ~established:true provided promised)
              end
        in
        let* actual = snapshot_contract ~implementation:true name in
        let* () =
          match actual with
          | NamespaceContract.Module summary ->
              require_all ~context ~owner ~loc:binding.mod_inst_loc environment
                summary.separation
          | Functor _ -> Rewriter.return ()
        in
        let* expected = snapshot_contract binding.mod_inst_type in
        let* expected_owner =
          effective_path ~implementation:false binding.mod_inst_type
        in
        let expected =
          match (actual, expected) with
          | NamespaceContract.Module _, Functor summary -> summary.result
          | _ -> expected
        in
        (* Sealed public resolution exposes the interface; retain the implementation edge. *)
        let provided, actual_path = (actual, name) in
        compatible ~declarations ~owner ~loc:binding.mod_inst_loc environment ~actual_path
          ~expected_path:expected_owner ~established:true provided expected
  in
  Rewriter.eval_with_user_state ~init:pending
    (let* () =
       walk empty_environment
         (QualIdent.from_ident program.Module.mod_decl.mod_decl_name)
         program
     in
     Rewriter.current_user_state)

(** Validate conditional headers and close newly exposed realization requirements. *)
let validate ~draft program =
  let open Rewriter.Syntax in
  let rec fixed_point pending program =
    let* namespaces, _ = NamespaceClosure.imported_summaries () in
    let declarations = Map.data namespaces in
    let* next = validate_pass ~declarations program pending in
    let equal = Map.equal Requirements.equal pending next in
    if equal then Rewriter.return program
    else
      let* program =
        NamespaceClosure.freeze ~refresh:true ~requirements:next draft program
      in
      fixed_point next program
  in
  fixed_point (Map.empty (module QualIdent)) program
