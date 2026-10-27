open Base
open Ast

type t = {
  namespaces : NamespaceContract.namespace_decl Map.M(QualIdent).t;
  equations : NamespaceEquations.t;
  entailment : NamespaceEntailment.t;
  callables : NamespaceContract.callable_summary Map.M(QualIdent).t;
}
(** Draft inference; installing a frozen contract requires subsequent validation. *)

let namespace draft name = Map.find draft.namespaces name
let callable draft name = Map.find draft.callables name

type callable_seed = {
  kind : Callable.call_kind;
  origin : NamespaceOrigins.t option;
  formals : Type.var_decl list;
  returns : Type.var_decl list;
  required : Callable.mask;
  inferred : Callable.mask;
  granted : Callable.mask;
  opens : Callable.mask option;
}

type collection = {
  namespaces : NamespaceContract.namespace_decl Map.M(QualIdent).t;
  seeds : callable_seed Map.M(QualIdent).t;
}

let formal_names formals =
  List.map formals ~f:(fun formal -> formal.Type.var_name) |> Set.of_list (module Ident)

let expressible_formals decl atomic =
  List.filter decl.Callable.call_decl_formals ~f:(fun formal ->
      not (atomic && formal.Type.var_implicit))
  |> formal_names

let application_entries (name, kind, args) =
  let dependencies = (Callable.MaskHead.Dependencies name, args) in
  match kind with
  | Callable.Invariant -> [ Callable.invariant_mask_entry name args; dependencies ]
  | Pred -> [ dependencies ]
  | Func | Proc | Lemma -> assert false

let required_expression formals expression =
  let open Rewriter.Syntax in
  let+ applications = Masks.expr_inv_applications ~explicit_only:true expression in
  List.concat_map applications ~f:(fun (name, kind, args) ->
      application_entries (name, kind, Masks.truncate_to_formal_expressible formals args))
  |> Callable.mask_canon

let required_specs decl =
  let open Rewriter.Syntax in
  let+ masks =
    Rewriter.List.map decl.Callable.call_decl_precond ~f:(fun spec ->
        required_expression (expressible_formals decl spec.spec_atomic) spec.spec_form)
  in
  Callable.mask_canon (List.concat masks)

let granted_specs decl =
  let open Rewriter.Syntax in
  let+ masks =
    Rewriter.List.map decl.Callable.call_decl_postcond ~f:(fun spec ->
        let+ applications =
          Masks.expr_inv_applications ~explicit_only:false spec.spec_form
        in
        let expressible =
          Set.union
            (expressible_formals decl spec.spec_atomic)
            (formal_names decl.call_decl_returns)
        in
        List.concat_map applications ~f:(fun (name, kind, args) ->
            let prefix = Masks.truncate_to_formal_expressible expressible args in
            if List.length prefix = List.length args then
              application_entries (name, kind, args)
            else []))
  in
  Callable.mask_canon (List.concat masks)

let allocate symbol =
  let open Rewriter.Syntax in
  let* () =
    match symbol with
    | Module.CallDef
        {
          call_decl =
            { call_decl_kind = Pred | Invariant; call_decl_alias = None; _ } as decl;
          _;
        } ->
        let* owner = Rewriter.current_scope_id in
        let name = QualIdent.append owner decl.call_decl_name in
        let* state = Rewriter.current_user_state in
        let namespace : NamespaceContract.namespace_decl =
          { name; formals = decl.call_decl_formals; definition = Abstract }
        in
        Rewriter.set_user_state
          { state with namespaces = Map.set state.namespaces ~key:name ~data:namespace }
    | _ -> Rewriter.return ()
  in
  Rewriter.return symbol

let collect symbol =
  let open Rewriter.Syntax in
  let* () =
    match symbol with
    | Module.CallDef ({ call_decl = { call_decl_alias = None; _ } as decl; _ } as call) ->
        let* owner = Rewriter.current_scope_id in
        let name = QualIdent.append owner decl.call_decl_name in
        let* origin =
          match decl.call_decl_kind with
          | Proc | Lemma -> NamespaceOrigins.find ~owner decl
          | Func | Pred | Invariant -> Rewriter.return None
        in
        let* _ = Rewriter.enter_callable call in
        let* definition, inferred, granted, opens =
          match decl.call_decl_kind with
          | Pred | Invariant ->
              let+ definition =
                match call.call_def with
                | FuncDef { func_body = Some body } ->
                    let+ mask =
                      required_expression (formal_names decl.call_decl_formals) body
                    in
                    NamespaceContract.Defined mask
                | FuncDef { func_body = None } ->
                    Rewriter.return NamespaceContract.Abstract
                | ProcDef _ -> assert false
              in
              ( Some definition,
                [
                  ( Callable.MaskHead.Dependencies name,
                    List.map decl.call_decl_formals ~f:Expr.from_var_decl );
                ],
                [],
                None )
          | Proc | Lemma ->
              let* inferred = required_specs decl in
              let* granted = granted_specs decl in
              let+ opens =
                Rewriter.Option.map decl.call_decl_opens ~f:(fun clause ->
                    Masks.resolve_mask (Callable.opens_mask clause))
              in
              (None, inferred, granted, opens)
          | Func -> Rewriter.return (None, [], [], None)
        in
        let* _ = Rewriter.exit_callable call in
        let* state = Rewriter.current_user_state in
        let namespaces =
          match definition with
          | None -> state.namespaces
          | Some definition ->
              Map.update state.namespaces name ~f:(fun previous ->
                  { (Option.value_exn previous) with definition })
        in
        let seed =
          {
            kind = decl.call_decl_kind;
            origin;
            formals = decl.call_decl_formals;
            returns = decl.call_decl_returns;
            required = Option.value opens ~default:inferred;
            inferred;
            granted;
            opens;
          }
        in
        Rewriter.set_user_state
          { namespaces; seeds = Map.set state.seeds ~key:name ~data:seed }
    | _ -> Rewriter.return ()
  in
  Rewriter.return symbol

let resource_names mask = List.map mask ~f:(fun (head, _) -> Callable.mask_head_name head)

let definition_resources declaration =
  match declaration.NamespaceContract.definition with
  | Abstract -> []
  | Defined mask -> resource_names mask

(** Copy instantiated equations through the symbol's substitution, without inspecting
    instantiated bodies. Abstract declarations stay symbolic. *)
let complete_namespaces (state : collection) =
  let open Rewriter.Syntax in
  let pending =
    List.concat_map (Map.data state.namespaces) ~f:definition_resources
    @ List.concat_map (Map.data state.seeds) ~f:(fun seed ->
        resource_names (seed.inferred @ seed.required @ seed.granted))
  in
  let rec complete namespaces = function
    | [] -> Rewriter.return namespaces
    | name :: pending when Map.mem namespaces name -> complete namespaces pending
    | name :: pending ->
        let* declaration =
          Rewriter.in_scope_of name
            (let* _, symbol = Rewriter.resolve_and_find name in
             let* decl = Rewriter.Symbol.reify_callable_decl symbol in
             let original = Rewriter.Symbol.orig_qid symbol in
             match Map.find state.namespaces original with
             | None ->
                 Rewriter.return
                   {
                     NamespaceContract.name;
                     formals = decl.call_decl_formals;
                     definition = Abstract;
                   }
             | Some template ->
                 let requalify = QualIdent.requalify (Rewriter.Symbol.subst symbol) in
                 let* declaration =
                   NamespaceContract.map_state_namespace_decl
                     ~name:(fun name -> Rewriter.return (requalify name))
                     ~expr:(Rewriter.Expr.rewrite_qual_idents ~f:requalify)
                     ~typ:(Rewriter.Type.rewrite_qual_idents ~f:requalify)
                     template
                 in
                 let+ definition =
                   match declaration.definition with
                   | Abstract -> Rewriter.return NamespaceContract.Abstract
                   | Defined body ->
                       let+ body = Masks.resolve_mask body in
                       NamespaceContract.Defined body
                 in
                 { declaration with name; definition })
        in
        complete
          (Map.set namespaces ~key:name ~data:declaration)
          (definition_resources declaration @ pending)
  in
  complete state.namespaces pending

let covers entry grant =
  match Callable.mask_entry_meet entry grant with
  | Some meet -> Callable.compare_mask_entry meet grant = 0
  | None -> false

let summarize equations seed =
  let expanded = NamespaceEquations.expand_required equations seed.required in
  let requires =
    match (seed.kind, seed.opens) with
    | (Callable.Proc | Lemma), None ->
        List.filter expanded ~f:(fun (head, _) ->
            match head with
            | Callable.MaskHead.Invariant _ -> true
            | Dependencies _ -> false)
    | (Func | Pred | Invariant), _ | (Proc | Lemma), Some _ -> expanded
  in
  let inferred = NamespaceEquations.expand_required equations seed.inferred in
  let omitted =
    List.filter inferred ~f:(fun entry ->
        not (List.exists requires ~f:(fun permitted -> covers permitted entry)))
  in
  let grants, guarded_grants =
    List.partition_tf seed.granted ~f:(fun grant ->
        List.exists requires ~f:(fun entry -> covers entry grant) || List.is_empty omitted)
  in
  let guarded_grants =
    List.map guarded_grants ~f:(fun ((head, _) as grant) ->
        let conditions =
          List.map omitted ~f:(fun (other, _) ->
              {
                NamespaceContract.left = [ (head, []) ];
                right = [ (other, []) ];
                loc = QualIdent.to_loc (Callable.mask_head_name head);
              })
        in
        { NamespaceContract.grants = [ grant ]; conditions })
  in
  {
    NamespaceContract.kind = seed.kind;
    NamespaceContract.formals = seed.formals;
    returns = seed.returns;
    requires;
    grants;
    guarded_grants;
    separation = [];
  }

let inherit_summary seed origin summary =
  let open Rewriter.Syntax in
  let requalify = QualIdent.requalify origin.NamespaceOrigins.substitution in
  let* summary =
    NamespaceContract.map_state_callable_summary
      ~name:(fun name -> Rewriter.return (requalify name))
      ~expr:(Rewriter.Expr.rewrite_qual_idents ~f:requalify)
      ~typ:(Rewriter.Type.rewrite_qual_idents ~f:requalify)
      summary
  in
  let pairs =
    match
      List.zip
        (summary.NamespaceContract.formals @ summary.returns)
        (seed.formals @ seed.returns)
    with
    | Ok pairs -> pairs
    | Unequal_lengths ->
        Util.Error.internal_error
          (QualIdent.to_loc origin.name)
          "Inherited mask contracts have different binder arities"
  in
  let renaming =
    List.fold pairs
      ~init:(Map.empty (module QualIdent))
      ~f:(fun renaming (source, target) ->
        Map.set renaming
          ~key:(QualIdent.from_ident source.Type.var_name)
          ~data:(Expr.from_var_decl target))
  in
  let summary =
    NamespaceContract.map_callable_summary ~name:Fn.id ~typ:Fn.id
      ~expr:(fun expression -> Expr.alpha_renaming expression renaming)
      summary
  in
  Rewriter.return { summary with formals = seed.formals; returns = seed.returns }

(** Resolve declaration budgets before substituting their implementation resources. *)
let freeze_budgets ~equations ~seeds imported =
  let open Rewriter.Syntax in
  let rec freeze path completed name =
    match Map.find completed name with
    | Some summary -> Rewriter.return (completed, summary)
    | None ->
        if Set.mem path name then
          Util.Error.internal_error (QualIdent.to_loc name)
            "Cyclic inherited mask contract";
        let path = Set.add path name in
        let seed =
          match Map.find seeds name with
          | Some seed -> seed
          | None ->
              Util.Error.internal_error (QualIdent.to_loc name)
                ("Missing declaration for inherited mask contract "
               ^ QualIdent.to_string name)
        in
        let* completed, summary =
          match seed.origin with
          | None -> Rewriter.return (completed, summarize equations seed)
          | Some origin ->
              let* completed, parent = freeze path completed origin.name in
              let+ summary =
                Rewriter.in_scope_of name (inherit_summary seed origin parent)
              in
              (completed, summary)
        in
        Rewriter.return (Map.set completed ~key:name ~data:summary, summary)
  in
  let imported = Map.filter_keys imported ~f:(fun name -> not (Map.mem seeds name)) in
  Rewriter.List.fold_left (Map.keys seeds) ~init:imported ~f:(fun completed name ->
      let+ completed, _ = freeze (Set.empty (module QualIdent)) completed name in
      completed)

let infer ?(namespaces = []) ?(callables = []) program =
  let open Rewriter.Syntax in
  let init : collection =
    {
      namespaces =
        Map.of_alist_exn
          (module QualIdent)
          (List.map namespaces ~f:(fun declaration ->
               (declaration.NamespaceContract.name, declaration)));
      seeds = Map.empty (module QualIdent);
    }
  in
  let* state =
    Rewriter.eval_with_user_state ~init
      (let* _ = Rewriter.Module.rec_rewrite_symbols ~f:allocate program in
       let* _ = Rewriter.Module.rec_rewrite_symbols ~f:collect program in
       Rewriter.current_user_state)
  in
  let* namespaces = complete_namespaces state in
  let equations = NamespaceEquations.solve (Map.data namespaces) in
  let* callables =
    freeze_budgets ~equations ~seeds:state.seeds
      (Map.of_alist_exn (module QualIdent) callables)
  in
  let+ entailment = NamespaceEntailment.create (Map.data namespaces) in
  { namespaces; equations; entailment; callables }

(* Imported equations can expose aliases only after expansion. *)
let normalize_required draft mask =
  NamespaceEquations.normalize_required ~resolve:Masks.resolve_mask draft.equations mask

(** Reify only summary metadata; callable bodies are never needed at a call site. *)
let find_callable draft name =
  let open Rewriter.Syntax in
  let* _, symbol = Rewriter.resolve_and_find name in
  let original = Rewriter.Symbol.orig_qid symbol in
  match Map.find draft.callables original with
  | None -> Rewriter.return None
  | Some summary ->
      let requalify = QualIdent.requalify (Rewriter.Symbol.subst symbol) in
      let* summary =
        NamespaceContract.map_state_callable_summary
          ~name:(fun name -> Rewriter.return (requalify name))
          ~expr:(Rewriter.Expr.rewrite_qual_idents ~f:requalify)
          ~typ:(Rewriter.Type.rewrite_qual_idents ~f:requalify)
          summary
      in
      let* requires = normalize_required draft summary.requires in
      let* grants = Masks.resolve_mask summary.grants in
      let* separation =
        Rewriter.List.map summary.separation ~f:(fun requirement ->
            let* left = Masks.resolve_mask requirement.NamespaceContract.left in
            let+ right = Masks.resolve_mask requirement.right in
            { requirement with left; right })
      in
      let summary = { summary with NamespaceContract.requires; grants; separation } in
      let+ grants =
        if List.is_empty summary.guarded_grants then Rewriter.return grants
        else
          let* available =
            NamespaceEntailment.available_grants draft.entailment ~assumptions:[] summary
          in
          Masks.resolve_mask available
      in
      Some { summary with NamespaceContract.grants }
