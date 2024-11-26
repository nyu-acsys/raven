open Base
open Ast
open Util

type au_token = {
  token : Expr.t;
  callable : QualIdent.t;
  callable_args : expr list;
  implicit_bound_vars : expr list;
}

type invs = { inv_name : QualIdent.t; inv_args : Expr.t list }

type atomicity_check = {
  au_opened : au_token list;
  invs_opened : invs list;
  atomic_step_taken : bool;
  mask : QualIdentSet.t;
}

let take_atomic_step ~loc (state : atomicity_check) : atomicity_check =
  if List.is_empty state.au_opened && List.is_empty state.invs_opened then state
  else
    match state.atomic_step_taken with
    | false -> { state with atomic_step_taken = true }
    | true ->
        Error.verification_error loc
          "Attempting to take more than one atomic step with an open invariant \
           or atomic update"

let take_non_atomic_step ~loc (state : atomicity_check) : atomicity_check =
  if List.is_empty state.au_opened && List.is_empty state.invs_opened then state
  else
    Error.verification_error loc
      "Cannot take a non-atomic step inside an atomic block"

let open_inv ~loc (inv_name, inv_args) atomicity_state : atomicity_check =
  if
    List.exists atomicity_state.invs_opened ~f:(fun inv ->
        QualIdent.(inv.inv_name = inv_name)
        && List.for_all2_exn inv_args inv.inv_args ~f:Expr.alpha_equal)
    || not (Set.mem atomicity_state.mask inv_name)
  then
    Error.verification_error loc
      (Printf.sprintf
         !"Cannot open invariant %{Ident}. Invariant already opened or not in \
           mask"
         (inv_name |> QualIdent.unqualify))
  else
    {
      atomicity_state with
      invs_opened = { inv_name; inv_args } :: atomicity_state.invs_opened;
      mask = Set.remove atomicity_state.mask inv_name;
    }

let close_inv ~loc (inv_name, inv_args) atomicity_state : atomicity_check =
  if
    (not
       (List.exists atomicity_state.invs_opened ~f:(fun inv ->
            QualIdent.(inv.inv_name = inv_name)
            && List.for_all2_exn inv_args inv.inv_args ~f:Expr.alpha_equal)))
    && Set.exists atomicity_state.mask ~f:(QualIdent.equal inv_name)
  then
    (* Folding a new invariant *)
    (* Allowed if invariant not already opened, but exists in the mask *)
    atomicity_state
  else if
    (not
       (List.exists atomicity_state.invs_opened ~f:(fun inv ->
            QualIdent.(inv.inv_name = inv_name)
            && List.for_all2_exn inv_args inv.inv_args ~f:Expr.alpha_equal)))
    && not (Set.exists atomicity_state.mask ~f:(QualIdent.equal inv_name))
  then
    Error.error loc
      "Invariant not already opened; cannot be closed. Invariant not in mask; \
       cannot be allocated."
  else
    let invs_opened =
      List.filter atomicity_state.invs_opened ~f:(fun inv ->
          not
            (QualIdent.(inv.inv_name = inv_name)
            && List.for_all2_exn inv_args inv.inv_args ~f:Expr.alpha_equal))
    in

    let mask = Set.add atomicity_state.mask inv_name in

    if List.is_empty invs_opened && List.is_empty atomicity_state.au_opened then
      { atomicity_state with invs_opened; mask; atomic_step_taken = false }
    else { atomicity_state with invs_opened; mask }

let open_au ~loc (token, callable, callable_args, implicit_bound_vars)
    atomicity_state : atomicity_check =
  if
    List.exists atomicity_state.au_opened ~f:(fun au ->
        Expr.alpha_equal au.token token)
  then Error.error loc "Atomic token already opened"
  else
    {
      atomicity_state with
      au_opened =
        { token; callable; callable_args; implicit_bound_vars }
        :: atomicity_state.au_opened;
    }

let close_au ~loc token atomicity_state : atomicity_check =
  if
    not
      (List.exists atomicity_state.au_opened ~f:(fun au ->
           Expr.alpha_equal au.token token))
  then Error.error loc "Atomic token not already opened"
  else
    let au_opened =
      List.filter atomicity_state.au_opened ~f:(fun au ->
          not (Expr.alpha_equal au.token token))
    in

    if List.is_empty au_opened && List.is_empty atomicity_state.invs_opened then
      { atomicity_state with au_opened; atomic_step_taken = false }
    else { atomicity_state with au_opened }


let rewrite_au_cmnds (stmt : Stmt.t) : (Stmt.t, atomicity_check) Rewriter.t_ext
    =
  let open Rewriter.Syntax in
  let rec rewrite_au_cmnds (stmt : Stmt.t) :
      (Stmt.t, atomicity_check) Rewriter.t_ext =
    let* is_ghost_scope = Rewriter.is_ghost_scope in
    let* curr_callable_name = Rewriter.current_scope_id in

    let callable_info call_ident =
      let+ callable = Rewriter.find_and_reify_callable call_ident in
     
      let concrete_args =
        List.filter callable.call_decl.call_decl_formals ~f:(fun var_decl ->
            not var_decl.var_implicit)
      in
      let implicit_args =
        List.filter callable.call_decl.call_decl_formals ~f:(fun var_decl ->
            var_decl.var_implicit)
      in
      callable, concrete_args, implicit_args
    in

    Logs.debug (fun m ->
        m "Rewrites.rewrite_au_cmnds: curr_callable_name: %a" QualIdent.pr
          curr_callable_name);

    let loc = stmt.stmt_loc in

    let* atomicity_state = Rewriter.current_user_state in

    match stmt.stmt_desc with
    | Basic (New new_desc) ->
        let* new_lhs =
          let* symbol = Rewriter.find_and_reify new_desc.new_lhs in
          match symbol with
          | VarDef v -> Rewriter.return v
          | _ -> Error.error stmt.stmt_loc "Expected a var_def"
        in

        if new_lhs.var_decl.var_ghost then Rewriter.return stmt
        else
          let atomicity_state = take_atomic_step ~loc atomicity_state in
          let* _ = Rewriter.set_user_state atomicity_state in
          Rewriter.return stmt
    | Basic (Assign assign_desc) ->
        Rewriter.return stmt
    | Basic (Bind bind_desc) ->
        Rewriter.return stmt
    | Basic (FieldRead field_read_desc) -> (
        let* symbol = Rewriter.find_and_reify field_read_desc.field_read_lhs in
        match symbol with
        | VarDef v ->
            if v.var_decl.var_ghost then Rewriter.return stmt
            else
              let atomicity_state = take_atomic_step ~loc atomicity_state in
              let* _ = Rewriter.set_user_state atomicity_state in
              Rewriter.return stmt
        | _ -> Error.error stmt.stmt_loc "Expected a var_def")
    | Basic (FieldWrite field_write_desc) -> (
        let* symbol =
          Rewriter.find_and_reify field_write_desc.field_write_field
        in
        match symbol with
        | FieldDef fld ->
            if fld.field_is_ghost then Rewriter.return stmt
            else
              let atomicity_state = take_atomic_step ~loc atomicity_state in
              let* _ = Rewriter.set_user_state atomicity_state in
              Rewriter.return stmt
        | _ -> Error.error stmt.stmt_loc "Expected a var_def")
    | Basic (Cas cas_desc) ->
        let atomicity_state = take_atomic_step ~loc atomicity_state in
        let* _ = Rewriter.set_user_state atomicity_state in
        Rewriter.return stmt
    | Basic (Havoc qual_iden) ->
        Rewriter.return stmt
    | Basic (Call call_desc) ->
        let* symbol = Rewriter.find_and_reify call_desc.call_name in
        let call_decl, call_def =
          match symbol with
          | CallDef c -> (c.call_decl, c.call_def)
          | _ -> Error.error stmt.stmt_loc "Expected a call_def"
        in

        if
          not
            (Set.is_subset
               (Option.value_exn call_decl.call_decl_mask)
               ~of_:atomicity_state.mask)
        then
          let msg =
            let missing_inv =
              Set.choose
                (Set.diff
                   (Option.value_exn call_decl.call_decl_mask)
                   atomicity_state.mask)
              |> Option.value_exn |> QualIdent.unqualify
            in
            let call_id = call_desc.call_name |> QualIdent.unqualify in
            Printf.sprintf
              !"Cannot call %{Ident}. The invariant %{Ident} required by \
                %{Ident} is not available in the current mask"
              call_id missing_inv call_id
          in
          Error.verification_error stmt.stmt_loc msg
        else
          let* is_call_lhs_ghost =
            Rewriter.List.for_all call_desc.call_lhs ~f:(fun qual_iden ->
                let* symbol = Rewriter.find_and_reify qual_iden in
                match symbol with
                | VarDef v -> Rewriter.return v.var_decl.var_ghost
                | _ -> Error.error stmt.stmt_loc "Expected a var_def")
          in

          if
            (is_call_lhs_ghost && not (List.is_empty call_desc.call_lhs))
            || Poly.(call_decl.call_decl_kind = Lemma)
          then Rewriter.return stmt
          else if Callable.is_atomic call_decl then
            let atomicity_state = take_atomic_step ~loc atomicity_state in
            let* _ = Rewriter.set_user_state atomicity_state in
            Rewriter.return stmt
          else
            let atomicity_state = take_non_atomic_step ~loc atomicity_state in
            let* _ = Rewriter.set_user_state atomicity_state in
            Rewriter.return stmt
    | Basic (Return return_expr) ->
        let atomicity_state = take_atomic_step ~loc atomicity_state in
        let* _ = Rewriter.set_user_state atomicity_state in
        Rewriter.return stmt
    | Basic (Use use_desc) -> (
        let* symbol = Rewriter.find_and_reify use_desc.use_name in
        match symbol with
        | CallDef c -> (
            match c.call_decl.call_decl_kind with
            | Pred -> Rewriter.return stmt
            | Invariant ->
                let atomicity_state =
                  match use_desc.use_kind with
                  | Unfold ->
                      open_inv ~loc
                        (use_desc.use_name, use_desc.use_args)
                        atomicity_state
                  | Fold ->
                      close_inv ~loc
                        (use_desc.use_name, use_desc.use_args)
                        atomicity_state
                in

                let* _ = Rewriter.set_user_state atomicity_state in
                Rewriter.return stmt
            | _ -> Error.error stmt.stmt_loc "Expected a pred or invariant")
        | _ -> Error.error stmt.stmt_loc "Expected a call_def")
    | Basic (AUAction auaction_desc) -> (
        match auaction_desc.auaction_kind with
        | BindAU qual_iden ->
            let loc = Stmt.to_loc stmt in
            let* qual_iden_var =
              let+ symbol = Rewriter.find_and_reify qual_iden in
              match symbol with
              | VarDef v -> v
              | _ -> Error.error stmt.stmt_loc "Expected a var_def"
            in

            let* au_token_var =
              let+ symbol =
                Rewriter.find_and_reify
                  (QualIdent.from_ident
                     (ProgUtils.callable_au_token_ident ~loc
                        (QualIdent.unqualify curr_callable_name)))
              in
              match symbol with
              | VarDef v -> v
              | _ -> Error.error stmt.stmt_loc "Expected a var_def"
            in

            let assign_stmt =
              Stmt.mk_assign ~loc [ qual_iden ]
                (Expr.from_var_decl au_token_var.var_decl)
            in

            Rewriter.return assign_stmt
        | OpenAU (token, call_ident, bound_vars) -> (
            let* callable, concrete_args, implicit_args = callable_info call_ident in
            let exhale_stmt =
              Stmt.mk_exhale_expr
                ~cmnt:("OpenAU: " ^ Stmt.to_string stmt)
                ~loc
                (Expr.mk_app ~loc ~typ:Type.perm (AUPred curr_callable_name)
                   (token :: List.map concrete_args ~f:Expr.from_var_decl))
            in

            let alpha_renaming_map =
              List.fold2_exn implicit_args bound_vars
                ~init:(Map.empty (module QualIdent))
                ~f:(fun acc_map implicit_arg bound_var ->
                    Map.add_exn acc_map
                      ~key:(QualIdent.from_ident implicit_arg.var_name)
                      ~data:bound_var)
            in

            let inhale_stmts =
              List.filter_map callable.call_decl.call_decl_precond
                ~f:(fun spec ->
                    if not spec.spec_atomic then None
                    else
                      Some
                        (Stmt.mk_inhale_expr
                           ~cmnt:("OpenAU: " ^ Stmt.to_string stmt)
                           ~loc
                           (Expr.alpha_renaming spec.spec_form
                              alpha_renaming_map)))
            in

            let atomicity_state =
              open_au ~loc
                ( token,
                  curr_callable_name,
                  List.map concrete_args ~f:Expr.from_var_decl,
                  bound_vars )
                atomicity_state
            in
            let* _ = Rewriter.set_user_state atomicity_state in
            
            let new_stmt =
              Stmt.mk_block_stmt ~loc (exhale_stmt :: inhale_stmts)
            in

            Rewriter.return new_stmt)
        | AbortAU token | CommitAU (token, _) ->
            let opened_au_token =
              List.find atomicity_state.au_opened ~f:(fun au_token ->
                  Expr.alpha_equal au_token.token token)
            in

            let opened_au_token =
              match opened_au_token with
              | None ->
                  Error.error stmt.stmt_loc "No opened AU token found to abort"
              | Some opened_au_token -> opened_au_token
            in

            let* callable_decl =
              let+ symbol = Rewriter.find_and_reify opened_au_token.callable in
              match symbol with
              | CallDef c -> c.call_decl
              | _ -> Error.error stmt.stmt_loc "Expected a call_def"
            in

            let alpha_renaming_map =
              List.fold2_exn callable_decl.call_decl_formals
                (opened_au_token.callable_args
               @ opened_au_token.implicit_bound_vars)
                ~init:(Map.empty (module QualIdent))
                ~f:(fun acc_map formal_arg actual_arg ->
                  Map.add_exn acc_map
                    ~key:(QualIdent.from_ident formal_arg.var_name)
                    ~data:actual_arg)
            in

            let exhale_stmts, inhale_stmt, atomicity_state =
              match auaction_desc.auaction_kind with
              | AbortAU token ->
                  let loc = Stmt.to_loc stmt in

                  let exhale_stmts =
                    List.filter_map callable_decl.call_decl_precond
                      ~f:(fun spec ->
                        if not spec.spec_atomic then None
                        else
                          let error =
                            ( Error.Verification,
                              loc,
                              "An atomic precondition may no longer hold when \
                               aborting the atomic update." )
                          in
                          Some
                            (Stmt.mk_exhale_expr
                               ~cmnt:("AbortAU: " ^ Stmt.to_string stmt)
                               ~loc
                               ~spec_error:
                                 (Stmt.mk_const_spec_error error
                                 :: spec.spec_error)
                               (Expr.alpha_renaming spec.spec_form
                                  alpha_renaming_map)))
                  in

                  let inhale_stmt =
                    Stmt.mk_inhale_expr
                      ~cmnt:("AbortAU: " ^ Stmt.to_string stmt)
                      ~loc
                      (Expr.mk_app ~loc ~typ:Type.perm
                         (AUPred opened_au_token.callable)
                         (opened_au_token.token
                         :: opened_au_token.callable_args))
                  in

                  let atomicity_state = close_au ~loc token atomicity_state in

                  (exhale_stmts, inhale_stmt, atomicity_state)
              | CommitAU (token, ret_exprs) ->
                  let loc = Stmt.to_loc stmt in

                  let alpha_renaming_map =
                    List.fold2_exn callable_decl.call_decl_returns ret_exprs
                      ~init:alpha_renaming_map
                      ~f:(fun acc_map formal_arg actual_arg ->
                        Map.add_exn acc_map
                          ~key:(QualIdent.from_ident formal_arg.var_name)
                          ~data:actual_arg)
                  in

                  let exhale_stmts =
                    List.filter_map callable_decl.call_decl_postcond
                      ~f:(fun spec ->
                        if not spec.spec_atomic then None
                        else
                          let error =
                            ( Error.Verification,
                              loc,
                              "An atomic postcondition may not hold at this \
                               commit point." )
                          in
                          Some
                            (Stmt.mk_exhale_expr
                               ~cmnt:("CommitAU: " ^ Stmt.to_string stmt)
                               ~loc
                               ~spec_error:
                                 (Stmt.mk_const_spec_error error
                                 :: spec.spec_error)
                               (Expr.alpha_renaming spec.spec_form
                                  alpha_renaming_map)))
                  in

                  let inhale_stmt =
                    Stmt.mk_inhale_expr
                      ~cmnt:("CommitAU: " ^ Stmt.to_string stmt)
                      ~loc
                      (Expr.mk_app ~loc ~typ:Type.perm
                         (AUPredCommit opened_au_token.callable)
                         (opened_au_token.token
                          :: opened_au_token.callable_args
                         @ [ Expr.mk_tuple ret_exprs ]))
                  in

                  let atomicity_state = close_au ~loc token atomicity_state in

                  (exhale_stmts, inhale_stmt, atomicity_state)
              | _ -> assert false
            in

            let new_stmt =
              Stmt.mk_block_stmt ~loc (exhale_stmts @ [ inhale_stmt ])
            in

            let* _ = Rewriter.set_user_state atomicity_state in

            Rewriter.return new_stmt)
    | Block block_desc -> Rewriter.Stmt.descend stmt ~f:rewrite_au_cmnds
    | Cond cond_desc ->
        let* then_stmt =
          Rewriter.Stmt.descend cond_desc.cond_then ~f:rewrite_au_cmnds
        in
        let* then_atomicity_state = Rewriter.current_user_state in

        let* _ = Rewriter.set_user_state atomicity_state in
        let* else_stmt =
          Rewriter.Stmt.descend cond_desc.cond_else ~f:rewrite_au_cmnds
        in
        let* else_atomicity_state = Rewriter.current_user_state in

        let if_else_atomicity_states_equal =
          List.length then_atomicity_state.invs_opened
          = List.length else_atomicity_state.invs_opened
          && List.length then_atomicity_state.au_opened
             = List.length else_atomicity_state.au_opened
          && List.for_all2_exn then_atomicity_state.invs_opened
               else_atomicity_state.invs_opened ~f:(fun inv1 inv2 ->
                 QualIdent.equal inv1.inv_name inv2.inv_name
                 && List.for_all2_exn inv1.inv_args inv2.inv_args
                      ~f:Expr.alpha_equal)
          && List.for_all2_exn then_atomicity_state.au_opened
               else_atomicity_state.au_opened ~f:(fun au1 au2 ->
                 Expr.alpha_equal au1.token au2.token
                 && QualIdent.equal au1.callable au2.callable
                 && List.for_all2_exn au1.callable_args au2.callable_args
                      ~f:Expr.alpha_equal
                 && List.for_all2_exn au1.implicit_bound_vars
                      au2.implicit_bound_vars ~f:Expr.alpha_equal)
          (* && Bool.(then_atomicity_state.atomic_step_taken = else_atomicity_state.atomic_step_taken) *)
        in

        if if_else_atomicity_states_equal then
          let new_stmt =
            {
              stmt with
              stmt_desc =
                Cond
                  {
                    cond_desc with
                    cond_then = then_stmt;
                    cond_else = else_stmt;
                  };
            }
          in

          if is_ghost_scope then Rewriter.return new_stmt
          else
            let atomicity_state =
              take_non_atomic_step ~loc else_atomicity_state
            in
            let* _ = Rewriter.set_user_state atomicity_state in
            Rewriter.return new_stmt
        else
          Error.error stmt.stmt_loc
            "Inconsistent atomicity states in then and else branches"
    | _ -> Rewriter.Stmt.descend stmt ~f:rewrite_au_cmnds
  in

  let* stmt = rewrite_au_cmnds stmt in
  let* atomicity_state = Rewriter.current_user_state in

  if
    List.is_empty atomicity_state.au_opened
    && List.is_empty atomicity_state.invs_opened
  then Rewriter.return stmt
  else Error.error stmt.stmt_loc "Unclosed AU token or invariant"

let rewrite_atomicity_analysis (c : Callable.t) : Callable.t Rewriter.t =
  let open Rewriter.Syntax in
  let* scope_id = Rewriter.current_scope_id in
  Logs.debug (fun m ->
      m
        "Rewrites.rewrite_atomicity_analysis: Rewriting atomicity analysis for \
         callable: %a"
        QualIdent.pr scope_id);
  let+ c =
    Rewriter.eval_with_user_state
      ~init:
        {
          au_opened = [];
          invs_opened = [];
          atomic_step_taken = false;
          mask =
            Option.value c.call_decl.call_decl_mask
              ~default:(Set.empty (module QualIdent));
        }
      (Rewriter.Callable.rewrite_stmts ~f:rewrite_au_cmnds c)
  in

  c
