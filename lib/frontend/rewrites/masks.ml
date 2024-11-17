open Base
open Ast
open Util

let fixpoint_compute_masks (c : Callable.t) : (Callable.t, bool) Rewriter.t_ext
    =
  let open Rewriter.Syntax in
  let loc = c.call_decl.call_decl_loc in

  let* new_mask =
    match c.call_decl.call_decl_kind with
    | Pred | Invariant -> (
        let* fully_qual_iden =
          Rewriter.resolve loc (QualIdent.from_ident c.call_decl.call_decl_name)
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
                  Rewriter.find_and_reify loc pred)
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
              Rewriter.find_and_reify loc pred)
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
