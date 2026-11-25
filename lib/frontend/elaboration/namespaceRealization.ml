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
  region_overrides : NamespaceContract.namespace_decl list;
}

type obligation = {
  requirement : NamespaceContract.separation_requirement;
  scope : QualIdent.t;
  conditions : Expr.t list;
  pairs : (Callable.mask_entry * Callable.mask_entry) list;
  loc : Loc.t;
}
(** Instances of [requirement] separated under the precondition of [scope] if [conditions]
    hold. *)

type state = {
  pending : NamespaceContract.separation_requirement list Map.M(QualIdent).t;
  obligations : obligation list;
}

let empty_state = { pending = Map.empty (module QualIdent); obligations = [] }

let empty_environment =
  {
    roots = Set.empty (module QualIdent);
    universals = Set.empty (module QualIdent);
    assumptions = [];
    region_overrides = [];
  }

let below root name =
  List.is_prefix (QualIdent.to_list name) ~prefix:(QualIdent.to_list root)
    ~equal:Ident.equal

let map_contract transformations =
  Rewriter.NamespaceContract.rewrite_requalification ~transformations

let result contract =
  match NamespaceContract.view contract with
  | NamespaceContract.Module _ as contract -> contract
  | Functor summary -> summary.result
  | Requalified _ -> assert false

let own_namespaces contract =
  match NamespaceContract.view contract with
  | NamespaceContract.Module summary -> summary.namespaces
  | Functor _ -> []
  | Requalified _ -> assert false

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
          List.exists right ~f:(fun (other, _) ->
              Callable.equal_mask_head head other
              ||
              match (head, other) with
              | Callable.MaskHead.Invariant left, Invariant right ->
                  Option.is_some
                    (NamespaceRegions.projection context.regions ~descendant:left
                       ~ancestor:right)
                  || Option.is_some
                       (NamespaceRegions.projection context.regions ~descendant:right
                          ~ancestor:left)
              | _ -> false))

let remember ~owner constraints =
  let open Rewriter.Syntax in
  let* state = Rewriter.current_user_state in
  Rewriter.set_user_state
    {
      state with
      pending =
        Map.update state.pending owner ~f:(fun previous ->
            Requirements.union (Option.value previous ~default:[]) constraints);
    }

(** The argument inequalities that separate two entries of [requirement]'s instances, if
    the entries are disjoint at most up to their arguments. *)
let separating_condition ?(rename = Fn.id) context requirement (head, args)
    (other, other_args) =
  let open Rewriter.Syntax in
  match (head, other) with
  | Callable.MaskHead.Invariant name, Callable.MaskHead.Invariant _
    when Callable.equal_mask_head head other ->
      let arity =
        Map.find context.Entailment.namespaces name
        |> Option.value_map ~default:0 ~f:(fun (declaration : namespace_decl) ->
            List.length declaration.formals)
      in
      let compared =
        Int.min arity (Int.min (List.length args) (List.length other_args))
      in
      let args = List.take args compared and other_args = List.take other_args compared in
      (* Identical arguments name the same instance. *)
      Rewriter.return
        (if compared = 0 || List.equal (fun a b -> Expr.compare a b = 0) args other_args
         then None
         else
           Some
             (Some
                (Expr.mk_or
                   (List.map2_exn args other_args ~f:(fun arg other_arg ->
                        Expr.mk_not (Expr.mk_eq arg other_arg))))))
  | _ ->
      let+ separate =
        Entailment.entails ~rename context ~assumptions:[]
          {
            requirement with
            left = [ (head, []) ];
            right = [ (other, []) ];
            instances = None;
          }
      in
      if separate then Some None else None

(** Discharges [requirement] by the conditions its instances need, as an obligation of the
    callable that determines them. *)
let separate_instances ?(rename = Fn.id) ~context ~loc requirement =
  let open Rewriter.Syntax in
  match requirement.NamespaceContract.instances with
  | None -> Rewriter.return false
  | Some instances -> (
      let* state = Rewriter.current_user_state in
      if
        List.exists state.obligations ~f:(fun obligation ->
            NamespaceContract.compare_separation_requirement obligation.requirement
              requirement
            = 0)
      then Rewriter.return true
      else
        let* left = Entailment.normalize_mask ~rename context instances.instance_left in
        let* right = Entailment.normalize_mask ~rename context instances.instance_right in
        let pairs = List.cartesian_product left right in
        let* conditions =
          Rewriter.List.map pairs ~f:(fun (left, right) ->
              separating_condition ~rename context requirement left right)
        in
        match Option.all conditions with
        | None -> Rewriter.return false
        | Some conditions ->
            let separated = List.zip_exn pairs conditions in
            let+ () =
              Rewriter.set_user_state
                {
                  state with
                  obligations =
                    {
                      requirement;
                      scope = instances.scope;
                      conditions = List.filter_opt conditions;
                      pairs =
                        List.filter_map separated ~f:(fun (pair, condition) ->
                            Option.map condition ~f:(fun _ -> pair));
                      loc;
                    }
                    :: state.obligations;
                }
            in
            true)

let require ?(rename = Fn.id) ?(instances = false) ~context ~owner ~loc environment
    requirement =
  let open Rewriter.Syntax in
  let* satisfied =
    Entailment.entails ~rename context ~assumptions:environment.assumptions requirement
  in
  let* separated =
    if
      satisfied || (not instances)
      || not (Set.is_empty environment.roots && Set.is_empty environment.universals)
    then Rewriter.return false
    else separate_instances ~rename ~context ~loc requirement
  in
  if satisfied || separated then Rewriter.return ()
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
        remember ~owner [ requirement ]

let require_all ?(rename = Fn.id) ?instances ~context ~owner ~loc environment constraints
    =
  Rewriter.List.iter constraints
    ~f:(require ~rename ?instances ~context ~owner ~loc environment)

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
  let renaming = Expr.formal_renaming pairs in
  NamespaceContract.map_callable_summary ~name:Fn.id
    ~expr:(fun expression -> Expr.alpha_renaming expression renaming)
    ~typ:Fn.id expected

let grants_cover ?(rename = Fn.id) context ~assumptions provided promised =
  let open Rewriter.Syntax in
  let check assumptions required =
    let* available = Entailment.available_grants ~rename context ~assumptions provided in
    let* available = Entailment.normalize_predicates ~rename context available in
    let+ required = Entailment.normalize_predicates ~rename context required in
    Entailment.covered_regions context ~by:available required
  in
  let* unconditional = check assumptions promised.NamespaceContract.grants in
  let* exact =
    let* regional = Entailment.available_grants ~rename context ~assumptions provided in
    let* regional = Entailment.normalize_predicates ~rename context regional in
    let* exact = Entailment.normalize_predicates ~rename context provided.exact_grants in
    let+ required =
      Entailment.normalize_predicates ~rename context promised.exact_grants
    in
    List.for_all required ~f:(fun entry ->
        Entailment.covered ~by:exact [ entry ]
        || Entailment.covered_regions context ~by:regional [ entry ])
  in
  if not (unconditional && exact) then Rewriter.return false
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

let rec public_namespaces (summary : NamespaceContract.module_summary) =
  summary.namespaces
  @ List.concat_map summary.modules ~f:(fun (_, contract) ->
      match NamespaceContract.view contract with
      | Module nested -> public_namespaces nested
      | Functor _ -> []
      | Requalified _ -> assert false)

let namespace_map declarations =
  List.fold declarations
    ~init:(Map.empty (module QualIdent))
    ~f:(fun map (decl : namespace_decl) -> Map.set map ~key:decl.name ~data:decl)

let region_embedding ~sources ~actual_path ~loc environment
    (actual : NamespaceContract.module_summary)
    (expected : NamespaceContract.module_summary) =
  let open Rewriter.Syntax in
  let actual_pool = namespace_map (sources @ public_namespaces actual) in
  let public = public_namespaces expected in
  let own = namespace_map public in
  let constraint_names requirement =
    List.map (requirement.left @ requirement.right) ~f:(fun (head, _) ->
        Callable.mask_head_name head)
  in
  let refs =
    List.concat_map public ~f:NamespaceContract.references
    @ List.concat_map expected.callables ~f:(fun (_, summary) ->
        List.map
          (summary.requires @ summary.grants @ summary.exact_grants
          @ List.concat_map summary.guarded_grants ~f:(fun grant -> grant.grants))
          ~f:(fun (head, _) -> Callable.mask_head_name head)
        @ List.concat_map summary.separation ~f:constraint_names
        @ List.concat_map summary.guarded_grants ~f:(fun grant ->
            List.concat_map grant.conditions ~f:constraint_names))
    @ List.concat_map expected.separation ~f:constraint_names
  in
  let overrides = namespace_map (environment.region_overrides @ public) in
  let initial = overrides in
  let rec imports seen pool = function
    | [] -> (pool, seen)
    | name :: rest when Set.mem seen name -> imports seen pool rest
    | name :: rest -> (
        let seen = Set.add seen name in
        let declaration =
          match Map.find overrides name with
          | Some declaration -> Some declaration
          | None -> Map.find actual_pool name
        in
        match declaration with
        | None -> imports seen pool rest
        | Some declaration ->
            imports seen
              (Map.set pool ~key:name ~data:declaration)
              (NamespaceContract.references declaration @ rest))
  in
  let expected_pool, imports = imports (Set.empty (module QualIdent)) initial refs in
  let make pool =
    match NamespaceRegions.create (Map.data pool) with
    | Ok regions -> regions
    | Error error -> Error.type_error error.loc error.message
  in
  let expected_regions = make expected_pool in
  let actual_regions = make actual_pool in
  let rec invariant_names owner (summary : NamespaceContract.module_summary) =
    List.filter_map summary.callables ~f:(fun (name, callable) ->
        match callable.kind with
        | Callable.Invariant -> Some (QualIdent.append owner name)
        | _ -> None)
    @ List.concat_map summary.modules ~f:(fun (name, contract) ->
        match NamespaceContract.view contract with
        | Module nested -> invariant_names (QualIdent.append owner name) nested
        | Functor _ -> []
        | Requalified _ -> assert false)
  in
  let own_names = invariant_names actual_path expected in
  let visible =
    List.filter
      (own_names @ Set.to_list imports)
      ~f:(fun name -> Map.mem own name || not (below actual_path name))
    |> List.dedup_and_sort ~compare:QualIdent.compare
  in
  let* mapping =
    Rewriter.List.map visible ~f:(fun name ->
        let+ target = Entailment.canonical_name ~physical:true name in
        (name, target))
  in
  let regional =
    List.exists mapping ~f:(fun (source, target) ->
        NamespaceRegions.is_declared_regional expected_regions source
        || NamespaceRegions.is_declared_regional actual_regions target)
  in
  let () =
    if regional then
      match
        NamespaceRegionEmbedding.check ~expected:expected_regions ~actual:actual_regions
          ~visible ~mapping
      with
      | Ok () -> ()
      | Error error -> signature_error loc error.message
  in
  Rewriter.return (Map.data overrides, regional)

type check = {
  check_owner : QualIdent.t;
  check_roots : QualIdent.t list;
  check_universals : QualIdent.t list;
  check_assumptions : NamespaceContract.separation_requirement list;
  check_region_overrides : NamespaceContract.namespace_decl list;
  check_actual_path : QualIdent.t;
  check_expected_path : QualIdent.t;
  check_transformations : NamespaceContract.requalification list;
  check_established : bool;
  check_actual : NamespaceContract.t;
  check_expected : NamespaceContract.t;
}
[@@deriving compare]
(** The inputs of a compatibility check. Its outcome depends only on them and the
    entailment declarations, as module contracts are not read from the symbol table. *)

type checked = check list QualIdentHashtbl.t
(** Checks that passed, by their actual paths. A passed check need not be repeated: it
    adds its requirements to the pending ones, which only grow. *)

(** Structural shape/type compliance has already been checked by the nominal checker. *)
let rec compatible ?(checked : checked = Hashtbl.create (module QualIdent)) ~prepared
    ~owner ~loc environment ~actual_path ~expected_path ?(transformations = [])
    ~established actual expected =
  let open Rewriter.Syntax in
  let check =
    {
      check_owner = owner;
      check_roots = Set.to_list environment.roots;
      check_universals = Set.to_list environment.universals;
      check_assumptions = environment.assumptions;
      check_region_overrides = environment.region_overrides;
      check_actual_path = actual_path;
      check_expected_path = expected_path;
      check_transformations = transformations;
      check_established = established;
      check_actual = actual;
      check_expected = expected;
    }
  in
  let passed = Option.value (Hashtbl.find checked actual_path) ~default:[] in
  if List.mem passed check ~equal:(fun left right -> compare_check left right = 0) then
    Rewriter.return ()
  else
    let+ () =
      compatible_unchecked ~checked ~prepared ~owner ~loc environment ~actual_path
        ~expected_path ~transformations ~established actual expected
    in
    Hashtbl.add_multi checked ~key:actual_path ~data:check

and compatible_unchecked ~checked ~prepared ~owner ~loc environment ~actual_path
    ~expected_path ~transformations ~established actual expected =
  let open Rewriter.Syntax in
  let rename = NamespaceContract.requalify transformations in
  let* actual_path = effective_path actual_path in
  match (NamespaceContract.view actual, NamespaceContract.view expected) with
  | NamespaceContract.Module actual, Module expected ->
      let owner_transformations =
        NamespaceContract.Substitute [ (expected_path, QualIdent.to_list actual_path) ]
        :: transformations
      in
      let* expected =
        map_contract owner_transformations (NamespaceContract.Module expected)
      in
      let expected =
        match expected with
        | Module summary -> summary
        | Functor _ | Requalified _ -> assert false
      in
      let* region_overrides, _regional =
        region_embedding ~sources:prepared.Entailment.sources ~actual_path ~loc
          environment actual expected
      in
      let environment = { environment with region_overrides } in
      let overrides =
        List.filter expected.namespaces ~f:(fun declaration ->
            match declaration.NamespaceContract.definition with
            | Defined _ -> true
            | Abstract -> false)
      in
      (* Without renaming, the canonical forms of the declarations are shared. *)
      let* context, budget =
        if List.is_empty transformations then
          let* context = Entailment.extend prepared actual.namespaces in
          let+ budget = Entailment.extend ~overrides (Entailment.prepared context) [] in
          (context, budget)
        else
          let* context =
            Entailment.create ~rename
              (Entailment.overlay prepared.Entailment.sources actual.namespaces)
          in
          let+ budget =
            Entailment.create ~rename ~overrides (Map.data context.namespaces)
          in
          (context, budget)
      in
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
                      && not (Entailment.covered_regions context ~by:allowed required)
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
              compatible ~checked ~prepared ~owner ~loc environment
                ~actual_path:(QualIdent.append actual_path name)
                ~expected_path:(QualIdent.append actual_path name)
                ~transformations ~established:true provided promised)
  | Functor actual, Functor expected ->
      if List.length actual.parameters <> List.length expected.parameters then
        signature_error loc "functor parameter shapes differ";
      let pairs = List.zip_exn actual.parameters expected.parameters in
      let actual_parameter_roots =
        List.map pairs ~f:(fun ((actual, _), (expected, _)) ->
            ( QualIdent.append actual_path actual,
              QualIdent.to_list (QualIdent.append expected_path expected) ))
      in
      let actual_transformations =
        NamespaceContract.Substitute actual_parameter_roots :: transformations
      in
      let actual_rename = NamespaceContract.requalify actual_transformations in
      let expected_roots =
        List.map expected.parameters ~f:(fun (name, _) ->
            QualIdent.append expected_path name)
      in
      let expected_transformations =
        NamespaceContract.Except_below
          (expected_roots, [ (expected_path, QualIdent.to_list actual_path) ])
        :: transformations
      in
      let* actual =
        map_contract actual_transformations (NamespaceContract.Functor actual)
      in
      let* expected =
        map_contract expected_transformations (NamespaceContract.Functor expected)
      in
      let actual =
        match actual with
        | Functor summary -> summary
        | Module _ | Requalified _ -> assert false
      in
      let expected =
        match expected with
        | Functor summary -> summary
        | Module _ | Requalified _ -> assert false
      in
      let* context =
        Entailment.create ~rename:actual_rename
          (prepared.Entailment.sources @ own_namespaces actual.result)
      in
      (* An impossible promised condition cannot justify a realization. *)
      let* () =
        Rewriter.List.iter expected.separation ~f:(fun requirement ->
            let+ conflict = overlaps ~rename:actual_rename context requirement in
            if conflict then report ~loc requirement)
      in
      let inputs =
        List.concat_map expected.parameters ~f:(fun (_, contract) ->
            match NamespaceContract.view contract with
            | Module summary -> summary.separation
            | Functor _ -> []
            | Requalified _ -> assert false)
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
            compatible ~checked ~prepared ~owner ~loc environment ~actual_path:path
              ~expected_path:path ~transformations:actual_transformations
              ~established:true supplied demanded)
      in
      let without_formal_members parameters contract =
        match NamespaceContract.view contract with
        | NamespaceContract.Module result ->
            Module
              {
                result with
                modules =
                  List.filter result.modules ~f:(fun (name, _) ->
                      not (List.Assoc.mem parameters name ~equal:Ident.equal));
              }
        | Functor _ as result -> result
        | Requalified _ -> assert false
      in
      compatible ~checked ~prepared ~owner ~loc environment ~actual_path
        ~expected_path:actual_path ~transformations:actual_transformations
        ~established:true
        (without_formal_members actual.parameters actual.result)
        (without_formal_members expected.parameters expected.result)
  | Requalified _, _ | _, Requalified _ -> assert false
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

let validate_pass ~checked ~declarations program pending =
  let open Rewriter.Syntax in
  let* prepared = Entailment.prepare declarations in
  let* context = Entailment.extend prepared [] in
  let rec walk environment owner (m : Module.t) =
    Rewriter.in_scope_of
      (Module.unit_parameter_path owner)
      (let* contract =
         Rewriter.NamespaceContract.rewrite_requalification
           ~transformations:
             [ NamespaceContract.Substitute m.mod_decl.mod_decl_instance_subst ]
           (Option.value_exn m.Module.mod_decl.mod_decl_mask_contract)
       in
       let here =
         if m.mod_decl.mod_decl_is_interface || Module.is_functor m.mod_decl then
           { environment with roots = Set.add environment.roots owner }
         else environment
       in
       let* here =
         match contract with
         | Requalified _ -> assert false
         | NamespaceContract.Module _ -> Rewriter.return here
         | Functor summary ->
             let assumptions =
               List.concat_map summary.parameters ~f:(fun (_, parameter) ->
                   match NamespaceContract.view parameter with
                   | Module summary -> summary.separation
                   | Functor _ -> []
                   | Requalified _ -> assert false)
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
               Rewriter.NamespaceContract.rewrite_requalification
                 ~transformations:
                   [ NamespaceContract.Substitute m.mod_decl.mod_decl_instance_subst ]
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
             compatible ~checked ~prepared ~owner ~loc:m.mod_decl.mod_decl_loc comparison
               ~actual_path:owner ~expected_path:owner
               ~established:(not (Module.is_functor m.mod_decl))
               (result contract) (result promised))
       in
       let* () =
         Rewriter.List.iter m.mod_def ~f:(function
           | Module.SymbolDef (ModDef child) ->
               walk here (QualIdent.append owner child.mod_decl.mod_decl_name) child
           | SymbolDef (ModInst binding) -> application here owner binding
           | SymbolDef
               (CallDef _ | TypeDef _ | VarDef _ | FieldDef _ | ConstrDef _ | DestrDef _)
           | Import _ ->
               Rewriter.return ())
       in
       (* After the members, which report the requirements they contribute at their own
          locations. *)
       require_all ~instances:true ~context ~owner ~loc:m.mod_decl.mod_decl_loc here
         (requirements contract))
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
              | Requalified _ -> assert false
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
                            map_contract
                              [ NamespaceContract.Substitute bindings ]
                              promised
                          in
                          let* provided =
                            snapshot_contract ~implementation:true actual_path
                          in
                          compatible ~checked ~prepared ~owner ~loc:binding.mod_inst_loc
                            environment ~actual_path ~expected_path:actual_path
                            ~established:true provided promised)
              end
        in
        let* actual = snapshot_contract ~implementation:true name in
        let* () =
          match actual with
          | NamespaceContract.Module summary ->
              require_all ~instances:true ~context ~owner ~loc:binding.mod_inst_loc
                environment summary.separation
          | Functor _ -> Rewriter.return ()
          | Requalified _ -> assert false
        in
        let* expected = snapshot_contract binding.mod_inst_type in
        let* expected_owner =
          effective_path ~implementation:false binding.mod_inst_type
        in
        let* nominal =
          let* implementation = effective_path name in
          if QualIdent.equal implementation expected_owner then Rewriter.return true
          else
            let* table = Rewriter.get_table in
            let expected =
              SymbolTbl.resolve_and_find ~implementation:false ~read_only:true
                binding.mod_inst_type
                (SymbolTbl.goto binding.mod_inst_type table)
            in
            begin match
              (SymbolTbl.application_origin binding.mod_inst_type table, expected)
            with
            | None, Some (_, original, _, _) when QualIdent.equal original expected_owner
              ->
                begin match SymbolTbl.application_origin name table with
                | None -> Rewriter.return false
                | Some (head, _) ->
                    let+ head = effective_path head in
                    QualIdent.equal head expected_owner
                end
            | _ -> Rewriter.return false
            end
        in
        let expected =
          match (actual, expected) with
          | NamespaceContract.Module _, Functor summary -> summary.result
          | _ -> expected
        in
        (* Sealed public resolution exposes the interface; retain the implementation edge. *)
        let provided, actual_path = (actual, name) in
        if nominal then Rewriter.return ()
        else
          compatible ~checked ~prepared ~owner ~loc:binding.mod_inst_loc environment
            ~actual_path ~expected_path:expected_owner ~established:true provided expected
  in
  Rewriter.eval_with_user_state ~init:{ empty_state with pending }
    (let* () =
       walk empty_environment
         (QualIdent.from_ident program.Module.mod_decl.mod_decl_name)
         program
     in
     Rewriter.current_user_state)

(** A lemma that proves [obligation] from the ordinary precondition of its callable. *)
let obligation_lemma obligation =
  let open Rewriter.Syntax in
  let+ callable = Rewriter.find_and_reify_callable obligation.scope in
  let decl = callable.call_decl in
  let entry (head, args) =
    let name = Ident.to_string (QualIdent.unqualify (Callable.mask_head_name head)) in
    name ^ "(" ^ String.concat ~sep:", " (List.map args ~f:Expr.to_source_string) ^ ")"
  in
  let separated =
    String.concat ~sep:", "
      (List.map obligation.pairs ~f:(fun (left, right) ->
           entry left ^ " and " ^ entry right))
  in
  let errors =
    [
      Stmt.mk_const_spec_error
        ( Error.Verification Error.Mask,
          obligation.loc,
          "Cannot establish invariant namespace separation between " ^ separated );
      Stmt.mk_const_spec_error
        ( Error.RelatedLoc,
          obligation.requirement.loc,
          "This generic check requires the namespaces to be disjoint" );
    ]
  in
  let check =
    Stmt.mk_assert_expr ~loc:obligation.loc ~spec_error:errors
      (Expr.mk_and obligation.conditions)
  in
  Module.CallDef
    {
      call_decl =
        Callable.mk_call_decl ~kind:Lemma
          ~name:(Ident.fresh obligation.loc "$separation")
          ~loc:obligation.loc ~formals:decl.call_decl_formals
          ~precond:
            (List.filter decl.call_decl_precond ~f:(fun spec -> not spec.spec_atomic))
          ~needs_mask:[] ~grants_mask:[] ();
      call_def =
        ProcDef { proc_body = Some (Stmt.mk_block_stmt ~loc:obligation.loc [ check ]) };
    }

(** Validate conditional headers and close newly exposed realization requirements; also
    returns the obligations that separate instances. *)
let validate ~draft program =
  let open Rewriter.Syntax in
  let checked = Hashtbl.create (module QualIdent) in
  let rec fixed_point previous pending program =
    let* namespaces, _ = NamespaceClosure.imported_summaries () in
    let declarations = Map.data namespaces in
    if
      not
        (List.equal
           (fun left right -> NamespaceContract.compare_namespace_decl left right = 0)
           previous declarations)
    then Hashtbl.clear checked;
    let* { pending = next; obligations } =
      validate_pass ~checked ~declarations program pending
    in
    let equal = Map.equal Requirements.equal pending next in
    if equal then Rewriter.return (program, obligations)
    else
      let* program =
        NamespaceClosure.freeze ~refresh:true ~requirements:next draft program
      in
      fixed_point declarations next program
  in
  fixed_point [] (Map.empty (module QualIdent)) program
