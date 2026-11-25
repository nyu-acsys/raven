open Base
open Ast
open Util
open NamespaceContract

type t = {
  namespaces : namespace_decl Map.M(QualIdent).t;
  equations : NamespaceEquations.t;
  regions : NamespaceRegions.t;
  callables : callable_summary Map.M(QualIdent).t;
  roots : Set.M(QualIdent).t;
      (** The module parameters and undefined module instances of the program, whose
          invariants have no fixed identity. *)
}

let rec prefixes name =
  name :: (if QualIdent.is_qualified name then prefixes (QualIdent.pop name) else [])

let roots (table : SymbolTbl.t) =
  Map.fold table.tbl_symbols
    ~init:(Set.empty (module QualIdent))
    ~f:(fun ~key:owner ~data roots ->
      match data with
      | Module.ModDef definition ->
          let roots =
            List.fold (Module.formals definition.mod_decl) ~init:roots
              ~f:(fun roots formal ->
                Set.add roots (QualIdent.append owner formal.Module.mod_inst_name))
          in
          List.fold definition.mod_def ~init:roots ~f:(fun roots -> function
            | Module.SymbolDef (ModInst { mod_inst_name; mod_inst_def = None; _ }) ->
                Set.add roots (QualIdent.append owner mod_inst_name)
            | _ -> roots)
      | _ -> roots)

let project_instances ?(physical = false) table name =
  List.fold (prefixes name) ~init:name ~f:(fun name prefix ->
      let name =
        if not physical then name
        else
          match SymbolTbl.module_binding prefix (SymbolTbl.goto prefix table) with
          | Some ({ mod_inst_def = Some (Alias target); _ }, requalify) ->
              QualIdent.requalify [ (prefix, QualIdent.to_list (requalify target)) ] name
          | Some _ | None -> name
      in
      match
        SymbolTbl.resolve_and_find ~implementation:true ~read_only:true prefix
          (SymbolTbl.goto prefix table)
      with
      | Some (_, _, Module.ModDef module_, substitution) ->
          let reify = QualIdent.requalify (SymbolTbl.qid_subst substitution) in
          let witness =
            List.map module_.mod_decl.mod_decl_instance_subst ~f:(fun (source, target) ->
                (reify source, QualIdent.to_list (reify (QualIdent.from_list target))))
          in
          QualIdent.requalify witness name
      | Some (_, _, _, _) | None -> name)

let canonical_name ?(rename = Fn.id) ?(physical = false) name =
  let open Rewriter.Syntax in
  let rec fixed seen name =
    let renamed = rename name in
    let* table = Rewriter.get_table in
    let renamed = project_instances ~physical table renamed in
    let resolved =
      match
        SymbolTbl.resolve_and_find ~implementation:true ~read_only:true renamed
          (SymbolTbl.goto renamed table)
      with
      | None -> renamed
      | Some (_, resolved, _, _) -> resolved
    in
    let next = rename resolved in
    if QualIdent.equal next name || Set.mem seen next then Rewriter.return next
    else fixed (Set.add seen name) next
  in
  fixed (Set.empty (module QualIdent)) name

let canonical_argument ~rename table name =
  (* Argument aliases share values without identifying abstract module owners. *)
  let name = project_instances table (rename name) in
  if QualIdent.is_qualified name then
    SymbolTbl.identity ~preserve_abstract_owners:true name table
  else name

let canonical_mask ?(rename = Fn.id) mask =
  let open Rewriter.Syntax in
  let* table = Rewriter.get_table in
  let rewrite_argument =
    Rewriter.Expr.rewrite_qual_idents ~f:(canonical_argument ~rename table)
  in
  let+ mask =
    Rewriter.List.map mask ~f:(fun (head, args) ->
        let physical = Callable.is_invariant_head head in
        let* name = canonical_name ~rename ~physical (Callable.mask_head_name head) in
        let+ args = Rewriter.List.map args ~f:rewrite_argument in
        (Callable.map_mask_head ~f:(fun _ -> name) head, args))
  in
  Callable.mask_canon mask

let formal_renaming source target =
  match List.zip source target with
  | Unequal_lengths ->
      Error.internal_error Loc.dummy "Namespace alias formal arities differ"
  | Ok pairs -> Expr.formal_renaming pairs

let canonical_ancestry ~rename ~physical ancestry =
  let open Rewriter.Syntax in
  let* table = Rewriter.get_table in
  map_state_ancestry
    ~name:(canonical_name ~rename ~physical)
    ~expr:(Rewriter.Expr.rewrite_qual_idents ~f:(canonical_argument ~rename table))
    ancestry

let canonical_declaration_with ~rename ~physical ~definition declaration =
  let open Rewriter.Syntax in
  Rewriter.in_scope_of declaration.name
    (let* name = canonical_name ~rename ~physical declaration.name in
     let* definition = definition declaration.definition in
     let* alias =
       Rewriter.Option.map declaration.alias ~f:(canonical_name ~rename ~physical)
     in
     let+ ancestry = canonical_ancestry ~rename ~physical declaration.ancestry in
     { declaration with name; definition; ancestry; alias })

let canonical_declaration ?(rename = Fn.id) declaration =
  let open Rewriter.Syntax in
  let definition = function
    | Abstract -> Rewriter.return Abstract
    | Defined body ->
        let+ body = canonical_mask ~rename body in
        Defined body
  in
  canonical_declaration_with ~rename ~physical:false ~definition declaration

let canonical_region_declaration ~rename declaration =
  (* Region coverage ignores bodies; their presence still determines merge precedence. *)
  let definition = function
    | Abstract -> Rewriter.return Abstract
    | Defined _ -> Rewriter.return (Defined [])
  in
  canonical_declaration_with ~rename ~physical:true ~definition declaration

type prepared = {
  sources : namespace_decl list;
  canonical : namespace_decl list;
  context : t;  (** The context of [sources] alone. *)
}
(** Declarations with their canonical forms and context, which contexts that do not rename
    share. *)

(** The context of the [sources] declarations, whose canonical forms are [declarations].
*)
let build ~rename ~overrides ~callables ~sources declarations =
  let open Rewriter.Syntax in
  let canonical = canonical_declaration ~rename in
  let source_declarations = sources in
  let* overrides = Rewriter.List.map overrides ~f:canonical in
  let merge map declaration =
    Map.update map declaration.name ~f:(function
      | None -> declaration
      | Some previous -> merge_declarations previous declaration)
  in
  let source_declarations =
    List.fold source_declarations ~init:(Map.empty (module QualIdent)) ~f:merge
  in
  let primary_declaration declaration =
    if Option.is_some declaration.alias then Rewriter.return None
    else
      match Map.find source_declarations declaration.name with
      | Some primary when Option.is_none primary.alias ->
          let+ ancestry =
            Rewriter.in_scope_of primary.name
              (canonical_ancestry ~rename ~physical:false primary.ancestry)
          in
          let renaming = formal_renaming primary.formals declaration.formals in
          let ancestry =
            map_ancestry ~name:Fn.id
              ~expr:(fun arg -> Expr.alpha_renaming arg renaming)
              ancestry
          in
          Some { declaration with ancestry }
      | Some _ -> Rewriter.return None
      | None -> Rewriter.return (Some declaration)
  in
  let* declarations = Rewriter.List.map declarations ~f:primary_declaration in
  let declarations = List.filter_opt declarations in
  let namespaces = List.fold declarations ~init:(Map.empty (module QualIdent)) ~f:merge in
  let* table = Rewriter.get_table in
  let rec complete seen namespaces = function
    | [] -> Rewriter.return namespaces
    | name :: pending when Set.mem seen name || Map.mem namespaces name ->
        complete seen namespaces pending
    | name :: pending ->
        let seen = Set.add seen name in
        let resolved =
          SymbolTbl.resolve_and_find ~read_only:true name (SymbolTbl.goto name table)
        in
        let* copied =
          match resolved with
          | Some (original, _, _, subst) ->
              begin match Map.find source_declarations original with
              | Some template ->
                  let requalify = QualIdent.requalify (SymbolTbl.qid_subst subst) in
                  let* declaration =
                    NamespaceContract.map_state_namespace_decl
                      ~name:(fun name -> Rewriter.return (requalify name))
                      ~expr:(Rewriter.Expr.rewrite_qual_idents ~f:requalify)
                      ~typ:(Rewriter.Type.rewrite_qual_idents ~f:requalify)
                      template
                  in
                  let declaration = { declaration with name } in
                  (* A name's own declaration is in the context already. *)
                  if
                    QualIdent.equal original name
                    && NamespaceContract.compare_namespace_decl declaration template = 0
                  then Rewriter.return None
                  else
                    let* declaration = canonical declaration in
                    primary_declaration declaration
              | None -> Rewriter.return None
              end
          | None -> Rewriter.return None
        in
        let namespaces, introduced =
          match copied with
          | None -> (namespaces, [])
          | Some declaration -> (merge namespaces declaration, references declaration)
        in
        complete seen namespaces (introduced @ pending)
  in
  let pending =
    List.concat_map (Map.data namespaces) ~f:(fun declaration ->
        declaration.name :: references declaration)
    @ List.concat_map overrides ~f:references
  in
  let* namespaces = complete (Set.empty (module QualIdent)) namespaces pending in
  let namespaces =
    List.fold overrides ~init:namespaces ~f:(fun map declaration ->
        match declaration.definition with
        | Abstract -> map
        | Defined _ ->
            Map.update map declaration.name ~f:(function
              | Some existing -> { existing with definition = declaration.definition }
              | None -> declaration))
  in
  let physical = canonical_region_declaration ~rename in
  let* regional = Rewriter.List.map (Map.data namespaces) ~f:physical in
  let* regional =
    Rewriter.List.map regional ~f:(fun declaration ->
        match Map.find source_declarations declaration.name with
        | Some primary when Option.is_none primary.alias -> physical primary
        | Some _ | None -> Rewriter.return declaration)
  in
  let regional = List.fold regional ~init:(Map.empty (module QualIdent)) ~f:merge in
  let* aliases =
    Rewriter.List.map (Map.data source_declarations) ~f:(fun declaration ->
        match declaration.alias with
        | None -> Rewriter.return None
        | Some _ when Map.mem regional declaration.name -> Rewriter.return None
        | Some target ->
            let+ target = canonical_name ~rename ~physical:true target in
            Some { declaration with alias = Some target; ancestry = Root })
  in
  let regions =
    match NamespaceRegions.create (Map.data regional @ List.filter_opt aliases) with
    | Ok regions -> regions
    | Error error -> Error.type_error error.loc error.message
  in
  Rewriter.return
    {
      namespaces;
      regions;
      equations = NamespaceEquations.solve (Map.data namespaces);
      callables = Map.of_alist_exn (module QualIdent) callables;
      roots = roots table;
    }

let create ?(rename = Fn.id) ?(overrides = []) ?(callables = []) declarations =
  let open Rewriter.Syntax in
  let* canonical = Rewriter.List.map declarations ~f:(canonical_declaration ~rename) in
  build ~rename ~overrides ~callables ~sources:declarations canonical

(** The [declarations] with their canonical forms and context. *)
let prepare declarations =
  let open Rewriter.Syntax in
  let* canonical = Rewriter.List.map declarations ~f:canonical_declaration in
  let+ context =
    build ~rename:Fn.id ~overrides:[] ~callables:[] ~sources:declarations canonical
  in
  { sources = declarations; canonical; context }

let overlay sources declarations =
  let names =
    Set.of_list
      (module QualIdent)
      (List.map declarations ~f:(fun (declaration : namespace_decl) -> declaration.name))
  in
  List.filter sources ~f:(fun declaration -> not (Set.mem names declaration.name))
  @ declarations

(** Like [create] without renaming on the [prepared] declarations and [declarations], with
    the canonical forms of the [prepared] ones. *)
let extend ?(overrides = []) prepared declarations =
  let open Rewriter.Syntax in
  if List.is_empty overrides && List.is_empty declarations then
    Rewriter.return prepared.context
  else
    let* canonical = Rewriter.List.map declarations ~f:canonical_declaration in
    let replaced =
      Set.of_list
        (module QualIdent)
        (List.map declarations ~f:(fun (declaration : namespace_decl) -> declaration.name))
    in
    let preserved =
      List.filter_map (List.zip_exn prepared.sources prepared.canonical)
        ~f:(fun (source, canonical) ->
          Option.some_if (not (Set.mem replaced source.name)) canonical)
    in
    build ~rename:Fn.id ~overrides ~callables:[]
      ~sources:(overlay prepared.sources declarations)
      (preserved @ canonical)

(** The declarations of [context], which are canonical, with [context]. *)
let prepared context =
  let declarations = Map.data context.namespaces in
  { sources = declarations; canonical = declarations; context }

let resolve_namespaces state mask =
  Callable.mask_canon
    (List.map mask ~f:(fun (head, args) ->
         let name = Callable.mask_head_name head in
         let target =
           match head with
           | Callable.MaskHead.Invariant _ ->
               Option.value
                 (NamespaceRegions.canonical_name state.regions name)
                 ~default:name
           | Dependencies _ -> name
         in
         (Callable.map_mask_head ~f:(fun _ -> target) head, args)))

(** Resource identity comes from raw predicate contracts, not body upper bounds. *)
let normalize_predicates ?(rename = Fn.id) state mask =
  let open Rewriter.Syntax in
  let* table = Rewriter.get_table in
  let frozen original =
    match Map.find state.callables original with
    | Some summary -> Some summary
    | None ->
        Option.bind
          (Map.find table.tbl_symbols (QualIdent.pop original))
          ~f:(function
            | Module.ModDef
                { mod_decl = { mod_decl_mask_contract = Some contract; _ }; _ } ->
                let rec result contract =
                  match NamespaceContract.view contract with
                  | Module summary -> Some summary
                  | Functor summary -> result summary.result
                  | Requalified _ -> assert false
                in
                Option.bind (result contract) ~f:(fun summary ->
                    List.Assoc.find summary.callables
                      (QualIdent.unqualify original)
                      ~equal:Ident.equal)
            | _ -> None)
  in
  let summary name =
    match
      SymbolTbl.resolve_and_find ~implementation:true ~read_only:true name
        (SymbolTbl.goto name table)
    with
    | Some (original, _, _, substitution) ->
        Option.map (frozen original) ~f:(fun summary ->
            let requalify = QualIdent.requalify (SymbolTbl.qid_subst substitution) in
            NamespaceContract.map_callable_summary ~name:requalify
              ~expr:(Expr.map_qual_idents ~f:requalify)
              ~typ:(Type.map_qual_idents ~f:requalify)
              summary)
    | None -> None
  in
  let matching_variables binders arguments =
    match List.zip binders arguments with
    | Unequal_lengths -> false
    | Ok pairs ->
        List.for_all pairs ~f:(fun (binder, argument) ->
            match argument with
            | Expr.App (Expr.Var variable, [], _) ->
                QualIdent.equal variable (QualIdent.from_ident binder.Type.var_name)
            | _ -> false)
  in
  let symbolic_resource (summary : callable_summary) =
    match (summary.kind, summary.requires, summary.grants, summary.guarded_grants) with
    | ( Callable.Pred,
        [ (Callable.MaskHead.Dependencies needed, inputs) ],
        [ (Callable.MaskHead.Dependencies granted, values) ],
        [] ) ->
        List.is_empty summary.exact_grants
        && QualIdent.equal needed granted
        && matching_variables summary.formals inputs
        && matching_variables (summary.formals @ summary.returns) values
    | _ -> false
  in
  let rec resolve seen original ((head, args) as entry) =
    match head with
    | Callable.MaskHead.Invariant _ -> Rewriter.return [ entry ]
    | Dependencies name when Set.mem seen name -> Rewriter.return [ original ]
    | Dependencies name ->
        begin match summary name with
        | Some ({ formals; returns; grants; _ } as contract)
          when symbolic_resource contract ->
            let* next =
              canonical_mask ~rename
                (NamespaceEquations.instantiate (formals @ returns) args grants)
            in
            let next = resolve_namespaces state next in
            if Callable.mask_equal [ entry ] next then Rewriter.return next
            else
              let+ next =
                Rewriter.List.map next ~f:(resolve (Set.add seen name) original)
              in
              Callable.mask_canon (List.concat next)
        | Some _ | None -> Rewriter.return [ entry ]
        end
  in
  let* mask = canonical_mask ~rename mask in
  let mask = resolve_namespaces state mask in
  let+ masks =
    Rewriter.List.map mask ~f:(fun entry ->
        resolve (Set.empty (module QualIdent)) entry entry)
  in
  Callable.mask_canon (List.concat masks)

let normalize_mask ?(rename = Fn.id) state mask =
  NamespaceEquations.normalize_required
    ~resolve:(normalize_predicates ~rename state)
    state.equations mask

let covered ~by mask =
  List.for_all mask ~f:(fun entry ->
      List.exists by ~f:(fun bound ->
          match Callable.mask_entry_meet bound entry with
          | None -> false
          | Some meet -> Callable.compare_mask_entry meet entry = 0))

let covered_regions context ~by mask =
  List.for_all mask ~f:(fun entry ->
      covered ~by [ entry ] || NamespaceRegions.covers_entry context.regions ~by entry)

let concrete_origin table name =
  let owners =
    if QualIdent.is_qualified name then prefixes (QualIdent.pop name) else []
  in
  List.for_all owners ~f:(fun owner ->
      match Map.find table.SymbolTbl.tbl_symbols owner with
      | Some (Module.ModDef definition) ->
          (not definition.mod_decl.mod_decl_is_interface)
          && Option.is_none definition.mod_decl.mod_decl_sealed_target
      | _ -> true)

let defined_invariant_origin table name =
  match Map.find table.SymbolTbl.tbl_symbols name with
  | Some
      (Module.CallDef
         {
           call_decl = { call_decl_kind = Invariant; call_decl_alias = None; _ };
           call_def = FuncDef { func_body = Some _ };
         }) ->
      true
  | _ -> false

let ground table name =
  let rec check seen name =
    if Set.mem seen name then false
    else
      let seen = Set.add seen name in
      match
        SymbolTbl.resolve_and_find ~implementation:true ~read_only:true name
          (SymbolTbl.goto name table)
      with
      | None -> false
      | Some (original, _, _, subst) ->
          List.for_all (prefixes original) ~f:(fun owner ->
              match Map.find table.SymbolTbl.tbl_symbols owner with
              | Some (Module.ModDef definition) ->
                  (not definition.mod_decl.mod_decl_is_interface)
                  && Option.is_none definition.mod_decl.mod_decl_sealed_target
                  && ((not (Module.is_functor definition.mod_decl))
                     || SymbolTbl.module_is_instantiated owner definition.mod_decl subst)
                  && List.for_all (Module.formals definition.mod_decl) ~f:(fun formal ->
                      let parameter = QualIdent.append owner formal.mod_inst_name in
                      let actual =
                        QualIdent.requalify (SymbolTbl.qid_subst subst) parameter
                      in
                      (not (QualIdent.equal parameter actual)) && check seen actual)
              | _ -> true)
  in
  check (Set.empty (module QualIdent)) name

let opaque_application table name =
  List.find (prefixes name) ~f:(fun prefix ->
      Option.is_some (SymbolTbl.find_sealed_view prefix (SymbolTbl.goto prefix table))
      &&
      match SymbolTbl.module_binding prefix (SymbolTbl.goto prefix table) with
      | Some ({ mod_inst_def = Some (ApplyUnit _); _ }, _) -> false
      | Some _ | None -> true)

let rigid table left right =
  match (left, right) with
  | Callable.MaskHead.Invariant left, Callable.MaskHead.Invariant right ->
      if
        QualIdent.equal left right
        || not
             (Option.equal QualIdent.equal
                (opaque_application table left)
                (opaque_application table right))
      then false
      else
        begin match
          ( SymbolTbl.resolve_and_find ~implementation:true ~read_only:true left
              (SymbolTbl.goto left table),
            SymbolTbl.resolve_and_find ~implementation:true ~read_only:true right
              (SymbolTbl.goto right table) )
        with
        | Some (source_left, _, _, _), Some (source_right, _, _, _) ->
            (concrete_origin table source_left
            || defined_invariant_origin table source_left)
            && (concrete_origin table source_right
               || defined_invariant_origin table source_right)
            && ((not (QualIdent.equal source_left source_right))
               || ground table left && ground table right
                  && Option.is_none (opaque_application table left))
        | _ -> false
        end
  | _ -> false

(* Invariant identity follows owners and constructor heads, not constructor arguments. *)
let identity_mentions ?(rename = Fn.id) ~roots mask =
  let open Rewriter.Syntax in
  if Set.is_empty roots then Rewriter.return false
  else
    let* canonical = canonical_mask ~rename mask in
    let+ table = Rewriter.get_table in
    (* Whether a root is reachable from [name]; a search that reaches none from a name
       reaches none from any it visited, so each name is visited once. *)
    let rec depends visited name =
      let name =
        if Module.is_unit_parameter_path name then QualIdent.pop name else name
      in
      if List.exists (prefixes name) ~f:(Set.mem roots) then (true, visited)
      else if Set.mem visited name then (false, visited)
      else
        any (Set.add visited name) (prefixes name) ~f:(fun visited owner ->
            let found, visited =
              match
                SymbolTbl.resolve_and_find ~implementation:true ~read_only:true owner
                  (SymbolTbl.goto owner table)
              with
              | Some (original, resolved, _, _) ->
                  any visited [ original; resolved ] ~f:depends
              | None -> (false, visited)
            in
            if found then (true, visited)
            else
              match SymbolTbl.application_origin owner table with
              | Some (head, _) -> depends visited head
              | None -> (false, visited))
    and any visited names ~f =
      match names with
      | [] -> (false, visited)
      | name :: names ->
          let found, visited = f visited name in
          if found then (true, visited) else any visited names ~f
    in
    fst
      (any
         (Set.empty (module QualIdent))
         (List.map (mask @ canonical) ~f:(fun (head, _) -> Callable.mask_head_name head))
         ~f:depends)

let rec entails ?(rename = Fn.id) state ~assumptions requirement =
  let open Rewriter.Syntax in
  let original_requirement = requirement in
  let canonical requirement =
    let* left = normalize_predicates ~rename state requirement.left in
    let+ right = normalize_predicates ~rename state requirement.right in
    { requirement with left; right }
  in
  let* assumptions = Rewriter.List.map assumptions ~f:canonical in
  let* requirement = canonical requirement in
  let assumed left right =
    List.exists assumptions ~f:(fun assumption ->
        covered_regions state ~by:assumption.left left
        && covered_regions state ~by:assumption.right right
        || covered_regions state ~by:assumption.right left
           && covered_regions state ~by:assumption.left right)
  in
  let* left = normalize_mask ~rename state requirement.left in
  let* right = normalize_mask ~rename state requirement.right in
  let same_invariant =
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
                      (NamespaceRegions.projection state.regions ~descendant:left
                         ~ancestor:right)
                    || Option.is_some
                         (NamespaceRegions.projection state.regions ~descendant:right
                            ~ancestor:left)
                | _ -> false))
  in
  if same_invariant then Rewriter.return false
  else
    let* table = Rewriter.get_table in
    let roots = state.roots in
    let* original_symbolic =
      identity_mentions ~rename ~roots
        (original_requirement.left @ original_requirement.right)
    in
    let* symbolic =
      Rewriter.List.map (left @ right) ~f:(fun ((head, _) as entry) ->
          let+ variable = identity_mentions ~rename ~roots [ entry ] in
          (head, variable))
    in
    let variable head =
      original_symbolic
      || List.exists symbolic ~f:(fun (other, variable) ->
          variable && Callable.equal_mask_head head other)
    in
    Rewriter.return
      (assumed requirement.left requirement.right
      || List.for_all left ~f:(fun ((head, _) as left) ->
          List.for_all right ~f:(fun ((other, _) as right) ->
              ((not (variable head || variable other)) && rigid table head other)
              || assumed [ left ] [ right ])))

and mentions ?(rename = Fn.id) ?(conservative = false) ~roots mask =
  let open Rewriter.Syntax in
  if Set.is_empty roots then Rewriter.return false
  else
    let original_mask = mask in
    let* mask = canonical_mask ~rename mask in
    let+ table = Rewriter.get_table in
    let rec depends seen name =
      let name =
        if Module.is_unit_parameter_path name then QualIdent.pop name else name
      in
      if List.exists (prefixes name) ~f:(Set.mem roots) then true
      else if Set.mem seen name then conservative
      else
        let resolved =
          SymbolTbl.resolve_and_find ~implementation:true ~read_only:true name
            (SymbolTbl.goto name table)
        in
        let seen = Set.add seen name in
        List.exists (prefixes name) ~f:(fun owner ->
            match SymbolTbl.application_origin owner table with
            | Some (head, arguments) ->
                depends seen head
                || List.exists arguments ~f:(fun (_, actual) -> depends seen actual)
            | None -> false)
        ||
        match resolved with
        | None -> false
        | Some (_, _, _, subst) ->
            List.exists (SymbolTbl.qid_subst subst) ~f:(fun (source, actual) ->
                if Module.is_unit_parameter_path source then false
                else
                  match actual with
                  | [] -> false
                  | _ ->
                      let actual = QualIdent.from_list actual in
                      (not (Module.is_unit_parameter_path actual)) && depends seen actual)
    in
    List.exists (original_mask @ mask) ~f:(fun (head, _) ->
        depends (Set.empty (module QualIdent)) (Callable.mask_head_name head))

(* Keep symbolic exposure in guards; dependency bounds only justify coverage. *)
let exposure state ~supplied resources =
  let open Rewriter.Syntax in
  let* resources = normalize_predicates state resources in
  let* available = normalize_mask state supplied in
  let+ resources =
    Rewriter.List.map resources ~f:(fun entry ->
        if covered_regions state ~by:supplied [ entry ] then Rewriter.return None
        else
          let+ bound = normalize_mask state [ entry ] in
          Option.some_if (not (covered_regions state ~by:available bound)) entry)
  in
  Callable.mask_canon (List.filter_opt resources)

(* As in [entails], distinct names are distinct invariants only where neither depends on a
   module parameter, which an instantiation could make the other. *)
let exact_disjoint state left right =
  let open Rewriter.Syntax in
  let roots = state.roots in
  let* original_symbolic = identity_mentions ~roots (left @ right) in
  let* left = normalize_mask state left in
  let* right = normalize_mask state right in
  let* symbolic =
    Rewriter.List.map (left @ right) ~f:(fun ((head, _) as entry) ->
        let+ variable = identity_mentions ~roots [ entry ] in
        (head, variable))
  in
  let variable head =
    original_symbolic
    || List.exists symbolic ~f:(fun (other, variable) ->
        variable && Callable.equal_mask_head head other)
  in
  let+ table = Rewriter.get_table in
  List.for_all left ~f:(fun (head, _) ->
      List.for_all right ~f:(fun (other, _) ->
          match (head, other) with
          | Callable.MaskHead.Invariant name, Invariant target ->
              (not (QualIdent.equal name target))
              && (((not (variable head || variable other)) && rigid table head other)
                 || Option.is_some
                      (NamespaceRegions.projection state.regions ~descendant:name
                         ~ancestor:target)
                 || Option.is_some
                      (NamespaceRegions.projection state.regions ~descendant:target
                         ~ancestor:name))
          | _ -> false))

let available_grants ?(rename = Fn.id) state ~assumptions
    (summary : NamespaceContract.callable_summary) =
  let open Rewriter.Syntax in
  let+ guarded =
    Rewriter.List.map summary.guarded_grants ~f:(fun grant ->
        let+ available =
          Rewriter.List.for_all grant.conditions ~f:(entails ~rename state ~assumptions)
        in
        if available then grant.grants else [])
  in
  List.fold guarded ~init:summary.grants ~f:Callable.mask_union

let impossible_conditions ?(rename = Fn.id) state conditions =
  let open Rewriter.Syntax in
  let+ impossible =
    Rewriter.List.map conditions ~f:(fun condition ->
        let* left = normalize_mask ~rename state condition.left in
        let+ right = normalize_mask ~rename state condition.right in
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
                          (NamespaceRegions.projection state.regions ~descendant:left
                             ~ancestor:right)
                        || Option.is_some
                             (NamespaceRegions.projection state.regions ~descendant:right
                                ~ancestor:left)
                    | _ -> false)))
  in
  List.exists impossible ~f:Fn.id

let grant_conditions ~exact ~loc state ~exposure grant =
  let open Rewriter.Syntax in
  Rewriter.List.fold_left exposure ~init:(Some []) ~f:(fun accumulated (other, _) ->
      match accumulated with
      | None -> Rewriter.return None
      | Some conditions ->
          let head, _ = grant in
          let requirement : separation_requirement =
            { left = [ (head, []) ]; right = [ (other, []) ]; loc; instances = None }
          in
          let* separated =
            if exact then exact_disjoint state requirement.left requirement.right
            else entails state ~assumptions:[] requirement
          in
          if separated then Rewriter.return (Some conditions)
          else
            let* impossible =
              if not exact then impossible_conditions state [ requirement ]
              else
                let* left = normalize_mask state requirement.left in
                let+ right = normalize_mask state requirement.right in
                List.exists left ~f:(fun (head, _) ->
                    List.exists right ~f:(fun (other, _) ->
                        Callable.equal_mask_head head other))
            in
            if impossible then Rewriter.return None
            else Rewriter.return (Some (requirement :: conditions)))
