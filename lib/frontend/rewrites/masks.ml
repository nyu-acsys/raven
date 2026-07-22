open Base
open Ast
open Util

let fixpoint_compute_masks (c : Callable.t) : (Callable.t, bool) Rewriter.t_ext
    =
  let open Rewriter.Syntax in

  let* new_mask =
    match c.call_decl.call_decl_kind with
    | Pred | Invariant -> (
        let* fully_qual_iden =
          Rewriter.resolve (QualIdent.from_ident c.call_decl.call_decl_name)
        in

        let mask_set =
          match c.call_decl.call_decl_kind with
          | Pred -> Set.empty (module QualIdent)
          | Invariant -> Set.singleton (module QualIdent) fully_qual_iden
          | _ -> assert false
        in

        match c.call_def with
        | FuncDef { func_body = Some body } ->
            let* preds_list = ProgUtils.expr_preds_mentioned body in

            let* preds_symbols =
              Rewriter.List.map preds_list ~f:(fun pred ->
                  Rewriter.find_and_reify pred)
            in

            let mask_set =
              List.fold preds_symbols ~init:mask_set ~f:(fun acc pred ->
                  match pred with
                  | CallDef pred_callable -> (
                      match pred_callable.call_decl.call_decl_mask with
                      | None -> acc
                      | Some mask -> Set.union acc mask)
                  | _ -> assert false)
            in

            Rewriter.return mask_set
            (* assert false *)
        | FuncDef { func_body = None } -> Rewriter.return mask_set
        | ProcDef _ -> assert false)
    | Lemma | Proc ->
        let specs =
          c.call_decl.call_decl_precond @ c.call_decl.call_decl_postcond
        in

        let* preds_list =
          Rewriter.List.fold_left specs ~init:[] ~f:(fun acc spec ->
              let+ preds =
                ProgUtils.expr_preds_mentioned spec.spec_form
              in

              preds @ acc)
        in

        Logs.debug (fun m ->
            m "Masks.fixpoint_compute_masks: Callable: %a;  preds_list: %a"
              Ident.pr c.call_decl.call_decl_name
              (Util.Print.pr_list_comma QualIdent.pr)
              preds_list);

        let* preds_symbols =
          Rewriter.List.map preds_list ~f:(fun pred ->
              Rewriter.find_and_reify pred)
        in

        let mask_set =
          List.fold preds_symbols
            ~init:(Set.empty (module QualIdent))
            ~f:(fun acc pred ->
              match pred with
              | CallDef pred_callable -> (
                  match pred_callable.call_decl.call_decl_mask with
                  | None -> acc
                  | Some mask -> Set.union acc mask)
              | _ -> assert false)
        in

        Logs.debug (fun m ->
            m "Masks.fixpoint_compute_masks: Callable: %a;  mask_set: %a"
              Ident.pr c.call_decl.call_decl_name
              (Util.Print.pr_list_comma QualIdent.pr)
              (Set.elements mask_set));

        Rewriter.return mask_set
    | Func -> Rewriter.return (Set.empty (module QualIdent))
  in

  if
    Option.is_some c.call_decl.call_decl_mask
    && Set.equal new_mask (Option.value_exn c.call_decl.call_decl_mask)
  then Rewriter.return c
  else
    let c =
      { c with call_decl = { c.call_decl with call_decl_mask = Some new_mask } }
    in
    let* _ = Rewriter.set_user_state true in
    Rewriter.return c

let rec compute_iteration (m : Module.t) : (Module.t, bool) Rewriter.t_ext =
  let open Rewriter.Syntax in
  let* flag = Rewriter.current_user_state in

  if flag then
    let* _ = Rewriter.set_user_state false in
    let* m = Rewriter.Module.rewrite_callables ~f:fixpoint_compute_masks m in
    compute_iteration m
  else Rewriter.return m

let compute_masks (m : Module.t) : Module.t Rewriter.t =
  Rewriter.eval_with_user_state ~init:true (compute_iteration m)

(** Checks that no module implementing an interface lets a newly-provided
    concrete definition of one of the interface's own abstract invariants or
    predicates depend on (i.e. include in its mask) another invariant that the
    same interface declares. An interface's own members are checked once,
    against the interface's abstract view; a caller reasoning about one of the
    interface's abstract members has no way to know that a later, concrete
    implementation made its mask grow to cover another of the interface's own
    invariants -- so if this were allowed, the interface's own members could
    silently stop verifying once instantiated concretely, without ever being
    re-checked (see scope-test.rav / atomiticy_redesign.md for the motivating
    example).

    Scoped to modules declared as [module N : M { ... }] (i.e.
    [mod_decl_returns = Some M]). Functor instantiation doesn't go through
    this code path (see [Typing.merge_defs]) and isn't at risk the same way,
    since it only ever substitutes formals -- it never gives a fresh body to
    one of [M]'s own abstract members. *)

let owned_invariant_names (iface : Module.t) : Ident.t list =
  List.filter_map iface.mod_def ~f:(function
      | Module.SymbolDef
          (CallDef
            { call_decl = { call_decl_kind = Invariant; call_decl_name; _ }; _ })
        ->
          Some call_decl_name
      | _ -> None)

let abstract_pred_or_inv_names (iface : Module.t) : Ident.t list =
  List.filter_map iface.mod_def ~f:(function
      | Module.SymbolDef
          (CallDef
            ({
               call_decl = { call_decl_kind = (Pred | Invariant); call_decl_name; _ };
               _;
             } as call))
        when Callable.is_abstract call ->
          Some call_decl_name
      | _ -> None)

let find_call_by_name (mdef : Module.t) (name : Ident.t) : Callable.t option =
  List.find_map mdef.mod_def ~f:(function
      | Module.SymbolDef
          (CallDef ({ call_decl = { call_decl_name; _ }; _ } as call))
        when Ident.equal call_decl_name name ->
          Some call
      | _ -> None)

let check_interface_reach_back (n : Module.t) : (unit, 'a) Rewriter.t_ext =
  let open Rewriter.Syntax in
  match n.mod_decl.mod_decl_returns with
  | None -> Rewriter.return ()
  | Some iface_qual_ident ->
      let* iface = Rewriter.find_and_reify_module iface_qual_ident in
      let owned_names = owned_invariant_names iface in
      let candidate_names = abstract_pred_or_inv_names iface in
      let* owned =
        let+ owned_qual_idents =
          Rewriter.List.map owned_names ~f:(fun name ->
              Rewriter.resolve (QualIdent.from_ident name))
        in
        Set.of_list (module QualIdent) owned_qual_idents
      in
      Rewriter.List.iter candidate_names ~f:(fun name ->
          match find_call_by_name n name with
          | None -> Rewriter.return ()
          | Some call when Callable.is_abstract call -> Rewriter.return ()
          | Some call ->
              let* self_qual_ident =
                Rewriter.resolve (QualIdent.from_ident name)
              in
              let mask =
                Option.value call.call_decl.call_decl_mask
                  ~default:(Set.empty (module QualIdent))
              in
              let reach_back = Set.remove (Set.inter mask owned) self_qual_ident in
              if Set.is_empty reach_back then Rewriter.return ()
              else
                Error.type_error call.call_decl.call_decl_loc
                  (Stdlib.Format.asprintf
                     "%s %a implements interface %a's abstract %a, but its \
                      definition depends on %a, which %a also declares"
                     (Symbol.kind (Module.CallDef call))
                     Ident.pr name QualIdent.pr iface_qual_ident Ident.pr name
                     (Util.Print.pr_list_comma QualIdent.pr)
                     (Set.elements reach_back)
                     QualIdent.pr iface_qual_ident))

let rec check_module_reach_back (m : Module.t) : (unit, 'a) Rewriter.t_ext =
  let open Rewriter.Syntax in
  let* _ = Rewriter.enter_module m in
  let* () = check_interface_reach_back m in
  let* () =
    Rewriter.List.iter m.mod_def ~f:(function
        | Module.SymbolDef (ModDef mod_def) -> check_module_reach_back mod_def
        | _ -> Rewriter.return ())
  in
  let+ _ = Rewriter.exit_module m in
  ()

let check_no_interface_reach_back (m : Module.t) : Module.t Rewriter.t =
  let open Rewriter.Syntax in
  let+ () = check_module_reach_back m in
  m
