(** The rewrites that lower the front end's output to the form the SMT encoding is
    generated from. *)

open Base
open Ast
open Util

let rec rewrite_expand_types (tp_expr : type_expr) : type_expr Rewriter.t =
  !Rewriter.expand_type_expr_ref tp_expr

let rec rewrite_ret_stmts (stmt : Stmt.t) : Stmt.t Rewriter.t =
  let open Rewriter.Syntax in
  match stmt.stmt_desc with
  | Basic (Return ret_expr) ->
      let loc = Stmt.to_loc stmt in

      let* curr_proc_name = Rewriter.current_scope_id in

      let* callable_decl =
        Logs.debug (fun m ->
            m "Lowering.rewrite_ret_stmts: curr_proc_name: %a" QualIdent.pr curr_proc_name);

        Rewriter.find_and_reify_callable curr_proc_name |+> fun c -> c.call_decl
      in

      let ret_expr_list = Expr.unfold_tuple ret_expr in

      let truncated_returns, dropped_returns =
        List.split_n callable_decl.call_decl_returns (List.length ret_expr_list)
      in

      (*let fresh_dropped_returns =
        List.map dropped_formal_args ~f:(fun var_decl ->
            {
              var_decl with
              var_name =
                Ident.fresh stmt.stmt_loc var_decl.var_name.ident_name;
              var_loc = stmt.stmt_loc;
            })
      in*)
      let dropped_returns_exprs = List.map dropped_returns ~f:Expr.from_var_decl in

      let dropped_returns_vars =
        List.map dropped_returns ~f:(fun decl -> QualIdent.from_ident decl.var_name)
      in

      let ret_expr = Expr.mk_tuple (ret_expr_list @ dropped_returns_exprs) in

      (* Need to ensure that call_decl_returns and call_desc.call_lhs line up *)
      let renaming_map =
        List.fold2_exn callable_decl.call_decl_returns
          (ret_expr_list @ dropped_returns_exprs)
          ~init:(Map.empty (module QualIdent))
          ~f:(fun map var_decl arg_expr ->
            Map.add_exn map ~key:(QualIdent.from_ident var_decl.var_name) ~data:arg_expr)
      in

      (*let renaming_map =
        List.fold2_exn callable_decl.call_decl_returns ret_expr_list
          ~init:(Map.empty (module QualIdent))
          ~f:(fun map var_decl expr ->
            Map.add_exn map
              ~key:(QualIdent.from_ident var_decl.var_name)
              ~data:expr)
      in*)
      let postconds_spec = callable_decl.call_decl_postcond in

      let postcond, spec_error =
        if Callable.is_atomic callable_decl then
          let atomic_token_var =
            Expr.mk_var
              ~typ:(Type.atomic_token curr_proc_name)
              (QualIdent.from_ident
                 (ProgUtils.callable_au_token_ident ~loc callable_decl.call_decl_name))
          in

          let concrete_args =
            List.filter callable_decl.call_decl_formals ~f:(fun var_decl ->
                not var_decl.var_implicit)
          in
          let concrete_args_expr = List.map concrete_args ~f:Expr.from_var_decl in

          let error =
            ( Error.Verification,
              loc,
              "The atomic specification may not have been committed before reaching this \
               return point" )
          in
          ( [
              Expr.mk_app ~loc ~typ:Type.perm (Expr.AUPredCommit curr_proc_name)
                [ atomic_token_var; Expr.mk_tuple concrete_args_expr; ret_expr ];
            ],
            [ Stmt.mk_const_spec_error error ] )
        else
          ( List.map postconds_spec ~f:(fun spec ->
                Expr.alpha_renaming spec.spec_form renaming_map),
            let error =
              ( Error.Verification,
                loc,
                "A postcondition may not hold at this return point" )
            in
            [ Stmt.mk_const_spec_error error ] )
      in

      let bind_stmt =
        match dropped_returns with
        | [] -> Stmt.mk_skip ~loc
        | _ ->
            Stmt.mk_bind ~loc dropped_returns_vars
              (Stmt.mk_spec ~atomic:false
                 ~cmnt:("bind added for return stmt: " ^ Stmt.to_string stmt)
                 ~spec_error (Expr.mk_and postcond))
      in

      let postconds_exhale_stmts =
        List.map postcond ~f:(fun expr ->
            Stmt.mk_exhale_expr
              ~cmnt:("exhape added for return stmt: " ^ Stmt.to_string stmt)
              ~loc ~spec_error expr)
      in

      let assume_false =
        Stmt.mk_assume_expr ~loc:stmt.stmt_loc (Expr.mk_bool ~loc:stmt.stmt_loc false)
      in

      let new_stmt =
        Stmt.mk_block_stmt ~loc:stmt.stmt_loc
          ((bind_stmt :: postconds_exhale_stmts) @ [ assume_false ])
      in

      Rewriter.return new_stmt
  | _ -> Rewriter.Stmt.descend stmt ~f:rewrite_ret_stmts

let rec rewrite_new_stmts (stmt : Stmt.t) : Stmt.t Rewriter.t =
  let open Rewriter.Syntax in
  match stmt.stmt_desc with
  | Basic (New new_desc) ->
      let* () =
        Rewriter.Logs.debug (fun printers m ->
            m "Lowering.rewrite_new_stmts: new_desc: %a" printers.pr_stmt stmt)
      in

      let assume_non_null_stmt =
        Stmt.mk_assume_expr ~loc:stmt.stmt_loc ~cmnt:"AssumeNonNull Stmt; from new stmt"
          (Expr.mk_not
             (Expr.mk_eq (Expr.mk_null ()) (Expr.mk_var ~typ:Type.ref new_desc.new_lhs)))
      in
      let* validity_check_optns =
        Rewriter.List.map new_desc.new_args ~f:(fun (fld_qi, e_opt) ->
            match e_opt with
            | None -> Rewriter.return None
            | Some e ->
                let+ field_symbol = Rewriter.find_and_reify_field fld_qi in

                let field_ra_valid_qi =
                  let field_ra = ProgUtils.field_get_ra_qual_iden field_symbol in
                  ProgUtils.get_ra_valid_fn_qual_ident field_ra
                in
                let assert_stmt =
                  let error =
                    ( Error.Verification,
                      stmt.stmt_loc,
                      "Could not prove validity of initially-allocated value" )
                  in
                  Stmt.mk_assert_expr ~loc:stmt.stmt_loc
                    ~cmnt:("new() stmt: " ^ Stmt.to_string stmt)
                    ~spec_error:[ Stmt.mk_const_spec_error error ]
                    (Expr.mk_app ~loc:stmt.stmt_loc ~typ:Type.bool
                       (Expr.Var field_ra_valid_qi) [ e ])
                in
                Some assert_stmt)
      in
      let validity_check_stmts = List.filter_map validity_check_optns ~f:(fun f -> f) in
      let havoc_stmt =
        Stmt.mk_havoc ~loc:stmt.stmt_loc
          (* ~cmnt:"RefVar Havoc Stmt; from new stmt" *)
          new_desc.new_lhs
      in

      let* new_inhale_stmts =
        Rewriter.List.map new_desc.new_args ~f:(fun (field_name, expr_optn) ->
            let* field_val =
              match expr_optn with
              | Some expr -> Rewriter.return expr
              | None -> ProgUtils.get_field_utils_id field_name
            in

            let* field_type =
              let* field_symbol = Rewriter.find_and_reify field_name in
              match field_symbol with
              | FieldDef f -> Rewriter.return f.field_type
              | _ -> Error.internal_error stmt.stmt_loc "expected a field_def"
            in

            let inhale_expr =
              Expr.mk_app ~typ:Type.perm ~loc:stmt.stmt_loc Expr.Own
                [
                  Expr.mk_var ~typ:Type.ref new_desc.new_lhs;
                  Expr.mk_var ~typ:field_type field_name;
                  field_val;
                ]
            in

            let inhale_stmt =
              Stmt.mk_inhale_expr
                ~cmnt:("new stmt: " ^ Stmt.to_string stmt)
                ~loc:stmt.stmt_loc inhale_expr
            in

            Rewriter.return inhale_stmt)
      in

      Rewriter.return
        (Stmt.mk_block_stmt ~loc:stmt.stmt_loc
           (validity_check_stmts
           @ (havoc_stmt :: assume_non_null_stmt :: new_inhale_stmts)))
  | _ -> Rewriter.Stmt.descend stmt ~f:rewrite_new_stmts

(** Replaces a `fold p(x, y)` stmt with `exhale p(); inhale p.body`. *)
let rec rewrite_fold_unfold_stmts (stmt : Stmt.t) : Stmt.t Rewriter.t =
  let open Rewriter.Syntax in
  let loc = stmt.stmt_loc in

  match stmt.stmt_desc with
  | Basic (Use use_desc) ->
      let* pred_qual_ident = Rewriter.resolve use_desc.use_name in
      let* symbol = Rewriter.find_and_reify use_desc.use_name in

      let pred_decl, body =
        match symbol with
        | CallDef c ->
            let spec =
              match c.call_def with
              | ProcDef p ->
                  Error.internal_error stmt.stmt_loc
                    "expected a func_def inside a fold/unfold stmt"
              | FuncDef { func_body = None } ->
                  Error.error stmt.stmt_loc (*(QualIdent.to_loc use_desc.use_name)*)
                    ("Cannot (un)fold abstract predicate "
                    ^ (use_desc.use_name |> QualIdent.unqualify |> Ident.to_string))
                  (* TW: this should already be checked during typing *)
              | FuncDef { func_body = Some e } -> e
            in

            (c.call_decl, Expr.set_loc spec (Stmt.to_loc stmt))
        | _ -> Error.internal_error stmt.stmt_loc "expected a call_def"
      in

      begin match (pred_decl.call_decl_kind, pred_decl.call_decl_is_inline) with
      | Pred, true ->
          let error =
            ( Error.Generic,
              loc,
              "Cannot (un)fold inline predicate: "
              ^ Ident.to_string pred_decl.call_decl_name )
          in
          Logs.warn (fun m -> m "%s" (Error.to_string error));
          Rewriter.return (Stmt.mk_skip ~loc)
      | _ ->
          let truncated_formal_args, dropped_formal_args =
            List.split_n
              (pred_decl.call_decl_formals @ pred_decl.call_decl_returns)
              (List.length use_desc.use_args)
          in

          let new_dropped_args =
            List.map dropped_formal_args ~f:(fun var_decl ->
                {
                  var_decl with
                  var_name = Ident.fresh stmt.stmt_loc var_decl.var_name.ident_name;
                  var_loc = stmt.stmt_loc;
                })
          in

          let new_dropped_args_exprs = List.map new_dropped_args ~f:Expr.from_var_decl in
          let* _ =
            Rewriter.List.map new_dropped_args ~f:(fun var ->
                Rewriter.introduce_symbol
                  (Module.VarDef
                     { var_decl = var; var_init = None; var_is_free = NotFree }))
          in

          let new_renaming_map =
            List.fold2_exn
              (truncated_formal_args @ dropped_formal_args)
              (use_desc.use_args @ new_dropped_args_exprs)
              ~init:(Map.empty (module QualIdent))
              ~f:(fun map var_decl arg_expr ->
                Map.add_exn map
                  ~key:(QualIdent.from_ident var_decl.var_name)
                  ~data:arg_expr)
          in

          let new_body =
            Expr.alpha_renaming body new_renaming_map |> Fn.flip Expr.set_loc loc
          in

          let existential_var_idens_set = Expr.existential_vars new_body in

          (* Resolve a name written in a `[x := e]` clause against the bound variables of
         the predicate's body. Matching is by *base* name, since the user writes the
         name as it appears in the source while the body carries disambiguated ones
         (`vs^4`) -- but one base name can match several once an `auto` predicate has
         been inlined into the body, bringing its own bound variables along (see
         [rewrite_inline_preds_expr]). Those are invisible in the source the user is
         looking at, so the clash is not their mistake, but neither is it something to
         resolve by guessing: picking one arbitrarily substituted a variable of one type
         where another was meant, and the result surfaced as malformed SMT and an
         internal error rather than as any kind of diagnosis. *)
          let resolve_existential (written : Ident.t) : Ident.t option =
            match
              Set.to_list existential_var_idens_set
              |> List.filter ~f:(fun ex ->
                  String.(ex.Ident.ident_name = written.ident_name))
            with
            | [] -> None
            | [ v ] -> Some v
            | several ->
                let types = Expr.existential_vars_type new_body in
                let described =
                  List.map several ~f:(fun v ->
                      match Map.find types v with
                      | Some tp -> Printf.sprintf !"one of type %{Type}" tp
                      | None -> "one")
                  |> String.concat ~sep:", "
                in
                Error.type_error stmt.stmt_loc
                  (Printf.sprintf
                     !"%{Ident} does not name a single bound variable of %{QualIdent}: \
                       there are %d of that name in its body (%s), so this does not say \
                       which one is meant. Either the body binds the name twice, or an \
                       `auto` predicate inlined into it brings a bound variable of the \
                       same name along -- which is not visible in the source. Rename so \
                       that the name is unique"
                     written use_desc.use_name (List.length several) described)
          in

          let user_exist_binds, user_exist_witnesses =
            match use_desc.use_kind with
            | Fold -> ([], use_desc.use_witnesses_or_binds)
            | Unfold -> (use_desc.use_witnesses_or_binds, [])
          in

          let* user_exist_binds_renam_map =
            Rewriter.List.fold_left user_exist_binds
              ~init:(Map.empty (module QualIdent))
              ~f:(fun mp (bd_iden, exis_expr) ->
                let exis_iden = Expr.to_qual_ident exis_expr |> QualIdent.unqualify in
                match resolve_existential exis_iden with
                | None -> Rewriter.return mp
                | Some v ->
                    Logs.debug (fun m ->
                        m
                          "Lowering.rewrite_fold_unfold_stmts : \n\
                          \                bd_iden = %a\n\
                          \                exis_iden = %a\n\
                          \              "
                          Ident.pr bd_iden Ident.pr exis_iden);

                    let+ bd_var_decl =
                      let+ bd_var_symbol =
                        Rewriter.find_and_reify (QualIdent.from_ident bd_iden)
                      in

                      begin match bd_var_symbol with
                      | VarDef v -> v.var_decl
                      | _ -> Error.internal_error stmt.stmt_loc "expected a var_def"
                      end
                    in

                    let bd_var_expr = Expr.from_var_decl bd_var_decl in
                    Map.set mp ~key:(QualIdent.from_ident v) ~data:bd_var_expr)
          in

          let user_witness_renam_map =
            List.fold user_exist_witnesses
              ~init:(Map.empty (module QualIdent))
              ~f:(fun mp (iden, wtns_expr) ->
                match resolve_existential iden with
                | None -> mp
                | Some v -> Map.set mp ~key:(QualIdent.from_ident v) ~data:wtns_expr)
          in

          let body_fold_expr, body_unfold_expr =
            let exhale_expr = Expr.supply_witnesses user_witness_renam_map new_body in
            let inhale_expr = Expr.supply_witnesses user_exist_binds_renam_map new_body in

            (exhale_expr, inhale_expr)
          in

          let pred_expr =
            Expr.alpha_renaming
              (Expr.mk_app ~loc ~typ:Type.bool (Expr.Var use_desc.use_name)
                 (use_desc.use_args @ new_dropped_args_exprs))
              new_renaming_map
          in

          let new_stmt =
            match use_desc.use_kind with
            | Fold -> (
                let spec_error =
                  let error =
                    ( Error.Verification,
                      stmt.stmt_loc,
                      "Failed to fold predicate. The body of the predicate may not hold \
                       at this point" )
                  in
                  [ Stmt.mk_const_spec_error error ]
                in
                let spec_form = Stmt.mk_spec ~spec_error body_fold_expr in
                let bind_stmt =
                  Stmt.mk_bind ~loc:stmt.stmt_loc
                    (List.map new_dropped_args ~f:(fun var_decl ->
                         QualIdent.from_ident var_decl.var_name))
                    spec_form
                in

                let inhale_stmt =
                  Stmt.mk_inhale_expr ~loc
                    ~cmnt:("fold : " ^ Expr.to_string pred_expr)
                    pred_expr
                in

                let exhale_stmt =
                  Stmt.mk_exhale_expr ~loc
                    ~cmnt:("fold : " ^ Expr.to_string pred_expr)
                    ~spec_error ~spec_source:(pred_qual_ident, 0) body_fold_expr
                in
                match new_dropped_args with
                | [] -> Stmt.mk_block_stmt ~loc [ exhale_stmt; inhale_stmt ]
                | _ -> Stmt.mk_block_stmt ~loc [ bind_stmt; exhale_stmt; inhale_stmt ])
            | Unfold -> (
                let inhale_stmt =
                  let usr_binds_havocs =
                    List.map use_desc.use_witnesses_or_binds ~f:(fun (i, e) ->
                        Stmt.mk_havoc ~loc (QualIdent.from_ident i))
                  in

                  let pred_body_inhale_stmt =
                    Stmt.mk_inhale_expr ~loc
                      ~cmnt:("unfold : " ^ Expr.to_string pred_expr)
                      ~spec_source:(pred_qual_ident, 0) body_unfold_expr
                  in

                  Stmt.mk_block_stmt ~loc (usr_binds_havocs @ [ pred_body_inhale_stmt ])
                in

                let spec_error =
                  let error =
                    ( Error.Verification,
                      stmt.stmt_loc,
                      "Failed to unfold predicate. The predicate may not hold at this \
                       point" )
                  in
                  [ Stmt.mk_const_spec_error error ]
                in

                let bind_stmt =
                  Stmt.mk_bind ~loc:stmt.stmt_loc
                    (List.map new_dropped_args ~f:(fun var_decl ->
                         QualIdent.from_ident var_decl.var_name))
                    (Stmt.mk_spec pred_expr ~spec_error)
                in

                let exhale_stmt =
                  Stmt.mk_exhale_expr ~loc
                    ~cmnt:("unfold : " ^ Expr.to_string pred_expr)
                    ~spec_error pred_expr
                in
                match new_dropped_args with
                | [] -> Stmt.mk_block_stmt ~loc [ exhale_stmt; inhale_stmt ]
                | _ -> Stmt.mk_block_stmt ~loc [ bind_stmt; exhale_stmt; inhale_stmt ])
          in
          Rewriter.return new_stmt
      end
  | _ -> Rewriter.Stmt.descend stmt ~f:rewrite_fold_unfold_stmts

let rec rewrite_call_stmts (stmt : Stmt.t) : Stmt.t Rewriter.t =
  let open Rewriter.Syntax in
  match stmt.stmt_desc with
  | Basic (Call call_desc) -> (
      let* callee_qual_ident = Rewriter.resolve call_desc.call_name in
      let* symbol = Rewriter.find_and_reify call_desc.call_name in

      let call_decl, call_def =
        match symbol with
        | CallDef c ->
            if call_desc.call_is_spawn then
              ( { c.call_decl with call_decl_postcond = []; call_decl_returns = [] },
                c.call_def )
            else (c.call_decl, c.call_def)
        | _ -> Error.internal_error stmt.stmt_loc "expected a call_def"
      in

      let _, dropped_returns =
        List.split_n call_decl.call_decl_returns (List.length call_desc.call_lhs)
      in

      let* fresh_dropped_returns =
        Rewriter.List.map dropped_returns ~f:(fun var_decl ->
            let new_var_decl =
              {
                var_decl with
                var_name = Ident.fresh stmt.stmt_loc var_decl.var_name.ident_name;
                var_loc = stmt.stmt_loc;
              }
            in
            let+ _ =
              Rewriter.introduce_symbol
                (Module.VarDef
                   { var_decl = new_var_decl; var_init = None; var_is_free = NotFree })
            in
            new_var_decl)
      in

      let* lhs_list =
        Rewriter.List.map call_desc.call_lhs ~f:(fun qual_iden ->
            let* symbol = Rewriter.find_and_reify qual_iden in

            match symbol with
            | VarDef v -> Rewriter.return v.var_decl
            | _ ->
                Error.internal_error stmt.stmt_loc
                  ("expected a variable; found " ^ Symbol.to_string symbol))
      in
      let lhs_list = lhs_list @ fresh_dropped_returns in

      let* new_lhs_list =
        Rewriter.List.map lhs_list ~f:(fun lhs ->
            let new_var_name =
              Ident.fresh stmt.stmt_loc (lhs.var_name.ident_name ^ "$ret")
            in
            let new_var_decl = { lhs with var_name = new_var_name } in
            let* _ =
              Rewriter.introduce_symbol
                (Module.VarDef
                   { var_decl = new_var_decl; var_init = None; var_is_free = NotFree })
            in

            Rewriter.return (Expr.from_var_decl new_var_decl))
      in

      let* new_renaming_map, new_dropped_args =
        let truncated_formal_args, dropped_formal_args =
          List.split_n call_decl.call_decl_formals (List.length call_desc.call_args)
        in

        let fresh_dropped_args =
          List.map dropped_formal_args ~f:(fun var_decl ->
              {
                var_decl with
                var_name = Ident.fresh stmt.stmt_loc var_decl.var_name.ident_name;
                var_loc = stmt.stmt_loc;
              })
        in

        let fresh_dropped_args_exprs =
          List.map fresh_dropped_args ~f:Expr.from_var_decl
        in

        (* Need to ensure that call_decl_returns and call_desc.call_lhs line up *)
        let renaming_map =
          List.fold2_exn
            (truncated_formal_args @ dropped_formal_args @ call_decl.call_decl_returns)
            (call_desc.call_args @ fresh_dropped_args_exprs @ new_lhs_list)
            ~init:(Map.empty (module QualIdent))
            ~f:(fun map var_decl arg_expr ->
              Map.add_exn map ~key:(QualIdent.from_ident var_decl.var_name) ~data:arg_expr)
        in

        Rewriter.return (renaming_map, fresh_dropped_args)
      in

      let* () =
        Rewriter.Logs.debug (fun printers m ->
            m "Lowering.rewrite_call_stmts: new_renaming_map: %a"
              (Util.Print.pr_map ~key:QualIdent.pr ~value:printers.pr_expr)
              new_renaming_map)
      in

      match call_def with
      | ProcDef _ ->
          let* _ =
            Rewriter.List.map new_dropped_args ~f:(fun var ->
                Rewriter.introduce_symbol
                  (Module.VarDef
                     { var_decl = var; var_init = None; var_is_free = NotFree }))
          in

          (* let build_exhale_spec (spec: Stmt.spec) =
               (* renames args from old to new. Also, existentially quantifies over relevant implicit variables. *)
               let spec_form = Expr.alpha_renaming spec.spec_form renaming_map in

               let used_implicit_vars = List.filter (List.zip_exn quant_dropped_args new_dropped_args) ~f:(
                 fun (var_decl1, var_decl2) ->
                   Set.mem (Expr.local_vars spec_form) var_decl1.var_name
               ) in

               let eqs = List.map used_implicit_vars ~f:(fun (v_d1, v_d2) -> Expr.mk_eq (Expr.from_var_decl v_d1) (Expr.from_var_decl v_d2)) in

               let used_quant_vars, _ = List.unzip used_implicit_vars in

               let spec_form = Expr.mk_binder ~loc:stmt.stmt_loc ~typ:Type.bool Exists used_quant_vars (Expr.mk_and (spec_form :: eqs)) in

               { spec with spec_form }
             in

             let build_inhale_spec (spec: Stmt.spec) =
               let spec_form = Expr.alpha_renaming spec.spec_form renaming_map2 in

               { spec with spec_form }
             in *)
          let spec_error =
            match
              List.map call_decl.call_decl_precond ~f:(fun spec -> spec.spec_error)
            with
            | (_ :: _ as err) :: _ -> err
            | _ -> []
          in
          let spec_form =
            Stmt.mk_spec
              ~cmnt:("Bind stmt for Call: " ^ Stmt.to_string stmt)
              ~spec_error
              (Expr.mk_and
                 (List.map call_decl.call_decl_precond ~f:(fun spec ->
                      Expr.alpha_renaming spec.spec_form new_renaming_map)))
          in

          let bind_stmt =
            (* TODO: can we preserve the error messages for the individual preconditions here? *)
            Stmt.mk_bind ~loc:stmt.stmt_loc
              (List.map new_dropped_args ~f:(fun var_decl ->
                   QualIdent.from_ident var_decl.var_name))
              spec_form
          in

          let exhale_stmts =
            List.mapi call_decl.call_decl_precond ~f:(fun i spec ->
                (* Logs.debug (fun m -> m "Lowering.rewrite_call_stmts: Exhale_stmt=%a; Exhale_stmt_error_len = %i; Exhale_stmt_error=%s" Expr.pr spec.spec_form (List.length spec_error) (Error.to_string ((List.hd_exn spec_error) (QualIdent.from_ident call_decl.call_decl_name) stmt.stmt_loc)) ); *)
                Stmt.mk_exhale_expr ~loc:stmt.stmt_loc
                  ~cmnt:("Exhale stmt for Call: " ^ Stmt.to_string stmt)
                  ~spec_error:spec.spec_error ~spec_source:(callee_qual_ident, i)
                  (Expr.alpha_renaming spec.spec_form new_renaming_map))
          in

          (* One inhale per postcond clause (rather than a single inhale of their
             conjunction) so each can carry its own [spec_source] -- `assume (p && q)`
             and `assume p; assume q` are equivalent, so this is not an observable
             behavior change. *)
          let num_precond = List.length call_decl.call_decl_precond in
          let inhale_stmts =
            List.mapi call_decl.call_decl_postcond ~f:(fun j spec ->
                Stmt.mk_inhale_expr ~loc:stmt.stmt_loc
                  ~cmnt:("Inhale stmt for Call: " ^ Stmt.to_string stmt)
                  ~spec_source:(callee_qual_ident, num_precond + j)
                  (Expr.alpha_renaming spec.spec_form new_renaming_map))
          in

          let reassign_lhs_stmt =
            Stmt.mk_assign ~loc:stmt.stmt_loc ~is_init:call_desc.call_is_init
              (List.map lhs_list ~f:(fun decl -> QualIdent.from_ident decl.var_name))
              (Expr.mk_tuple new_lhs_list)
          in

          (* TODO: Need to havoc ret vars before inhaling postconditions *)
          let new_stmt =
            Stmt.mk_block_stmt ~loc:stmt.stmt_loc
              (* (if (List.is_empty call_decl.call_decl_precond ) then *)
              (* [inhale_stmt] *)
              (* else *)
              (match (new_dropped_args, lhs_list) with
              | [], [] -> exhale_stmts @ inhale_stmts
              | [], _ -> exhale_stmts @ inhale_stmts @ [ reassign_lhs_stmt ]
              | _, [] -> (bind_stmt :: exhale_stmts) @ inhale_stmts
              | _, _ -> (bind_stmt :: exhale_stmts) @ inhale_stmts @ [ reassign_lhs_stmt ])
          in

          Rewriter.return new_stmt
      | FuncDef _ ->
          (* No exhale here: func/pred/invariant contracts can't carry a `requires`
             (see [Typing.check_no_requires_on_pure_callables]), so there is nothing to
             check at this call site. *)
          let ret_typ =
            Type.mk_prod stmt.stmt_loc
              (List.map call_decl.call_decl_returns ~f:(fun var_decl -> var_decl.var_type))
          in

          let new_assign_stmt =
            Stmt.mk_assign ~loc:stmt.stmt_loc
              (List.map new_lhs_list ~f:Expr.to_qual_ident)
              (Expr.mk_app ~loc:stmt.stmt_loc ~typ:ret_typ (Expr.Var call_desc.call_name)
                 call_desc.call_args)
          in

          let reassign_lhs_stmt =
            Stmt.mk_assign ~loc:stmt.stmt_loc
              (List.map lhs_list ~f:(fun decl -> QualIdent.from_ident decl.var_name))
              (Expr.mk_tuple new_lhs_list)
          in

          let new_stmt =
            Stmt.mk_block_stmt ~loc:stmt.stmt_loc
              (match lhs_list with
              | [] -> [ new_assign_stmt ]
              | _ -> [ new_assign_stmt; reassign_lhs_stmt ])
          in

          Rewriter.return new_stmt)
  | _ -> Rewriter.Stmt.descend stmt ~f:rewrite_call_stmts

let rewrite_callable_pre_post_conds (c : Callable.t) : Callable.t Rewriter.t =
  let open Rewriter.Syntax in
  match c.call_def with
  | ProcDef proc -> (
      match proc.proc_body with
      | None -> Rewriter.return c
      | Some body ->
          let loc = Stmt.to_loc body in
          let* own_qual_ident = Rewriter.current_scope_id in
          let num_precond = List.length c.call_decl.call_decl_precond in
          let pre_conds =
            List.filter_mapi c.call_decl.call_decl_precond ~f:(fun i spec ->
                if spec.spec_atomic then None
                else
                  let spec = { spec with spec_source = Some (own_qual_ident, i) } in
                  Some
                    (Stmt.mk_inhale_spec
                       ~cmnt:("precond: " ^ Expr.to_string spec.spec_form)
                       ~loc:(Expr.to_loc spec.spec_form) spec))
          and post_conds =
            List.filter_mapi c.call_decl.call_decl_postcond ~f:(fun j spec ->
                if spec.spec_atomic then None
                else
                  let spec =
                    { spec with spec_source = Some (own_qual_ident, num_precond + j) }
                  in
                  Some
                    (Stmt.mk_exhale_spec
                       ~cmnt:("postcond: " ^ Expr.to_string spec.spec_form)
                       ~loc:(Stmt.to_loc body |> Loc.to_end)
                       spec))
          in

          let* pre_conds, post_conds =
            if not (Callable.is_atomic c.call_decl) then
              Rewriter.return (pre_conds, post_conds)
            else
              let* callable_fully_qual_name = Rewriter.current_scope_id in

              let atomic_token_var =
                Expr.mk_var
                  ~typ:(Type.atomic_token callable_fully_qual_name)
                  (QualIdent.from_ident
                     (ProgUtils.callable_au_token_ident ~loc c.call_decl.call_decl_name))
              in

              let concrete_args =
                List.filter c.call_decl.call_decl_formals ~f:(fun var_decl ->
                    not var_decl.var_implicit)
              in
              let concrete_args_expr = List.map concrete_args ~f:Expr.from_var_decl in

              let inhale_au =
                Stmt.mk_inhale_expr ~cmnt:"au_precond" ~loc
                  (Expr.mk_app ~loc ~typ:Type.perm (Expr.AUPred callable_fully_qual_name)
                     [ atomic_token_var; Expr.mk_tuple concrete_args_expr ])
              in

              let exhale_au =
                let ret_vars =
                  List.map c.call_decl.call_decl_returns ~f:(fun var_decl ->
                      Expr.from_var_decl var_decl)
                in
                let ret_expr = Expr.mk_tuple ~loc ret_vars in
                let error =
                  ( Error.Verification,
                    loc |> Loc.to_end,
                    "The atomic specification may not have been committed before \
                     reaching this return point" )
                in
                Stmt.mk_exhale_expr ~cmnt:"au_postcond" ~loc
                  ~spec_error:[ Stmt.mk_const_spec_error error ]
                  (Expr.mk_app ~loc ~typ:Type.perm
                     (Expr.AUPredCommit callable_fully_qual_name)
                     [ atomic_token_var; Expr.mk_tuple concrete_args_expr; ret_expr ])
              in

              Rewriter.return (inhale_au :: pre_conds, exhale_au :: post_conds)
          in

          let new_body = Stmt.mk_block_stmt ~loc (pre_conds @ [ body ] @ post_conds) in
          let new_proc =
            Callable.
              {
                call_decl = c.call_decl;
                call_def = ProcDef { proc_body = Some new_body };
              }
          in
          Rewriter.return new_proc)
  | FuncDef func -> Rewriter.return c

let rec rewrite_add_pred_implicit_args (expr : Expr.t) : Expr.t Rewriter.t =
  let open Rewriter.Syntax in
  match expr with
  | App (Var qual_iden, args, expr_attr) ->
      let* symbol = Rewriter.find_and_reify qual_iden in
      begin match symbol with
      | CallDef callable
        when Poly.(
               callable.call_decl.call_decl_kind = Callable.Pred
               || callable.call_decl.call_decl_kind = Callable.Invariant) ->
          let* callable = Rewriter.find_and_reify_callable qual_iden in
          let* () =
            Rewriter.Logs.debug (fun printers m ->
                m "Lowering.rewrite_add_pred_implicit_args called on: %a; callable = %a"
                  printers.pr_expr expr printers.pr_callable callable)
          in
          if
            List.length
              (callable.call_decl.call_decl_formals @ callable.call_decl.call_decl_returns)
            = List.length args
          then Rewriter.return expr
          else
            let dropped_args =
              List.drop
                (callable.call_decl.call_decl_formals
               @ callable.call_decl.call_decl_returns)
                (List.length args)
            in
            let new_dropped_args =
              List.map dropped_args ~f:(fun var_decl ->
                  {
                    var_decl with
                    var_name = Ident.fresh expr_attr.expr_loc var_decl.var_name.ident_name;
                    var_loc = expr_attr.expr_loc;
                  })
            in
            Rewriter.return
              (Expr.mk_binder ~loc:expr_attr.expr_loc ~typ:Type.perm Exists
                 new_dropped_args
                 (App
                    ( Var qual_iden,
                      args @ List.map new_dropped_args ~f:Expr.from_var_decl,
                      expr_attr )))
      | _ -> Rewriter.return expr
      end
  | _ -> Rewriter.Expr.descend expr ~f:rewrite_add_pred_implicit_args

let rec rewrite_frac_field_types (symbol : Module.symbol) : Module.symbol Rewriter.t =
  let open Rewriter.Syntax in
  match symbol with
  | ModDef _ | ModInst _ | TypeDef _ | ConstrDef _ | DestrDef _ | VarDef _ | CallDef _ ->
      Rewriter.return symbol
  (* A manifest field shares the target's resource algebra: it takes the
     target's type as already rewritten rather than being wrapped in a Frac of
     its own, which would be a distinct RA over one heap. The field's type feeds
     the Frac module's name (see [rewrite_own_expr_4_arg]), so leaving it as the
     pre-rewrite type derives the wrong name. *)
  | FieldDef ({ field_alias = Some target; _ } as f) ->
      let* target_field = Rewriter.find_and_reify_field target in
      (* The alias generates no Frac module of its own, but a name derived from it can
         still be asked for: a callee whose contract was rewritten before this module
         existed carries `<A>.Frac$f` with `A` substituted to the alias's module, and
         nothing re-derives it from the resolved field at that point. Register the name
         as another spelling of the target's, the same way the field itself is
         registered as another spelling of the target. *)
      let* () =
        let* is_field_an_ra =
          ProgUtils.is_ra_type (Type.field_val target_field.field_type)
        in
        let* target = Rewriter.resolve target in
        let target_frac_mod =
          ProgUtils.frac_field_to_frac_mod_qual_ident ~loc:f.field_loc target
            target_field.field_type
        in
        (* A target from a unit lowered earlier, such as the library, has already been
           rewritten to its Frac module's type, so it has a Frac module despite looking
           like a resource algebra. *)
        let* already_rewritten = Rewriter.resolve_opt target_frac_mod in
        if is_field_an_ra && Option.is_none already_rewritten then Rewriter.return ()
        else
          Rewriter.add_transparent
            (ProgUtils.frac_field_to_frac_mod_ident ~loc:f.field_loc f.field_name
               target_field.field_type)
            target_frac_mod
      in
      Rewriter.return (Module.FieldDef { f with field_type = target_field.field_type })
  | FieldDef f ->
      let* is_field_an_ra = ProgUtils.is_ra_type (Type.field_val f.field_type) in

      let* () =
        Rewriter.Logs.debug (fun printers m ->
            m "Lowering.rewrite_frac_field_types:\n          is_field_an_ra: %a -> %b"
              printers.pr_type f.field_type is_field_an_ra)
      in

      if is_field_an_ra then Rewriter.return symbol
      else
        let* field_type = !Rewriter.expand_type_expr_ref f.field_type in
        let field_underlying_tp =
          match field_type with
          | App (Fld, [ tp_expr ], _) -> tp_expr
          | _ -> Error.type_error f.field_loc "Expected field identifier."
        in

        let* tp_module =
          ProgUtils.intros_type_module ~loc:f.field_loc ~f:Typing.process_symbol
            field_underlying_tp
        in

        let instantiated_frac_module =
          Module.ModInst
            {
              mod_inst_name =
                ProgUtils.frac_field_to_frac_mod_ident ~loc:f.field_loc f.field_name
                  field_type;
              mod_inst_type = Predefs.lib_cancellative_ra_mod_qual_ident;
              mod_inst_def =
                Some (Predefs.lib_frac_mod_qual_ident, [ Module.ModArg tp_module ]);
              mod_inst_is_interface = false;
              mod_inst_is_sealed = false;
              mod_inst_is_free = false;
              mod_inst_loc = f.field_loc;
            }
        in

        (* let* topscope_name = ProgUtils.find_highest_valid_scope_type_expr f.field_loc field_underlying_tp in

           let topscope_name = match topscope_name with
             | Some topscope_name -> topscope_name
             | None -> Error.type_error f.field_loc ("Could not find a valid scope to add field " ^ (Ident.to_string f.field_name) ^ " to.")

           in *)
        let* frac_mod_name =
          Rewriter.introduce_typecheck_symbol ~loc:f.field_loc ~f:Typing.process_symbol
            instantiated_frac_module
        in

        Logs.debug (fun m ->
            m "Lowering.rewrite_frac_field_types: \n          frac_mod_name: %a"
              QualIdent.pr frac_mod_name);

        let frac_type =
          Type.mk_fld f.field_loc
            (Type.mk_var (QualIdent.append frac_mod_name (Ident.make f.field_loc "T" 0)))
        in

        Rewriter.return (Module.FieldDef { f with field_type = frac_type })

(** Settle how each symbol an expression names is spelled, now that the resource algebras
    and heap utilities a field needs have been generated.

    Those artifacts are generated per field and named after it, so they exist only under
    the name of the field they belong to. A manifest field has none of its own -- it
    shares the ones belonging to the field it stands for -- and reaches them through
    aliases registered beside it. That is enough for the front end, which resolves; it is
    not enough for the backend, which keys on the name it is handed. A contract reaching a
    call site through a functor instantiated at a module with a manifest field is exactly
    that case: reifying the callee substitutes its formal for the argument module
    syntactically, so the contract comes out naming `Adapt.Frac$f` for a resource algebra
    that only ever existed as `Client.Frac$bit`.

    Only qualified names are touched -- an unqualified one is a formal or a local, which
    resolution has no business rewriting -- and anything that does not resolve is left
    exactly as it was. Types are left alone: they are canonical already, having been
    expanded on the way here. *)
let canonicalize_symbols (expr : Expr.t) : Expr.t Rewriter.t =
  let open Rewriter.Syntax in
  let canonicalize qual_ident =
    if List.is_empty (QualIdent.path qual_ident) then Rewriter.return qual_ident
    else
      let+ resolved = Rewriter.resolve_opt qual_ident in
      Option.value resolved ~default:qual_ident
  in
  Rewriter.Expr.rewrite_qual_idents_m ~f:canonicalize expr

let rec rewrite_own_expr_4_arg (expr : Expr.t) : Expr.t Rewriter.t =
  (* Rewrites expressions of the form `own(x, f, v, p)` to `own (x, f, Frac[f.type].frac_chunk(v, p))

     Essentially, makes a uniform 3-arg representation of all own expressions, frac-type as well as RA type.
  *)
  let open Rewriter.Syntax in
  let* () =
    Rewriter.Logs.debug (fun printers m ->
        m "Lowering.rewrite_own_expr_4_arg: run on expr: %a" printers.pr_expr expr)
  in

  match expr with
  | App (Own, [ expr1; expr2; expr3; expr4 ], expr_attr) ->
      let* () =
        Rewriter.Logs.debug (fun printers m ->
            m "Lowering.rewrite_own_expr_4_arg: found expr: %a" printers.pr_expr expr)
      in

      (* let field_type = match Expr.to_type expr2 with
           | App (Fld, [tp_expr], _) -> tp_expr
           | _ -> Error.type_error (Expr.to_loc expr2) "Expected field identifier."
         in *)
      let field_type = Expr.to_type expr2 in

      let* () =
        Rewriter.Logs.debug (fun printers m ->
            m "Lowering.rewrite_own_expr_4_arg: field_type1: %a" printers.pr_type
              field_type)
      in

      let* field_type = !Rewriter.expand_type_expr_ref field_type in
      let field_name = QualIdent.unqualify (Expr.to_qual_ident expr2) in

      let* () =
        Rewriter.Logs.debug (fun printers m ->
            m "Lowering.rewrite_own_expr_4_arg: field_type2: %a" printers.pr_type
              field_type)
      in

      let+ expr3 =
        let expr3_1 = expr3 in
        let expr3_2 = expr4 in

        let* () =
          Rewriter.Logs.debug (fun printers m ->
              m
                "Lowering.rewrite_own_expr_4_arg: intros_type_module started: tp_module: \
                 %a;\n\
                \ ... & frac_mod_ident: %a"
                printers.pr_type field_type QualIdent.pr
                (QualIdent.from_ident
                   (ProgUtils.frac_field_to_frac_mod_ident ~loc:(Expr.to_loc expr)
                      field_name field_type)))
        in

        let* frac_mod_name =
          (* Resolve the field before deriving its Frac module's name. A callee's
             contract reaches here with the instantiation substitution already
             applied syntactically (`H.f` -> `Adapt.f`), so the name was never put
             through the symbol table; without this a manifest field would look
             for an RA module beside the alias rather than beside the field it
             stands for. *)
          let* field_qual_ident = Rewriter.resolve (Expr.to_qual_ident expr2) in
          let frac_mod_name =
            ProgUtils.frac_field_to_frac_mod_qual_ident ~loc:(Expr.to_loc expr)
              field_qual_ident field_type
          in

          Logs.debug (fun m ->
              m "Lowering.rewrite_own_expr_4_args:  \n            frac_mod_name: %a"
                QualIdent.pr frac_mod_name);

          Rewriter.resolve frac_mod_name
        in

        let frac_type =
          Type.mk_var
            (QualIdent.append frac_mod_name (Ident.make (Expr.to_loc expr) "T" 0))
        in
        (* let frac_constr = Rewriter.find_and_reify (Expr.to_loc expr) (QualIdent.append frac_mod_name (Ident.make (Expr.to_loc expr) "frac_chunk" 0)) in *)
        let expr3 =
          Expr.mk_app ~loc:(Expr.to_loc expr) ~typ:frac_type
            (Expr.DataConstr
               (QualIdent.append frac_mod_name
                  (Ident.make (Expr.to_loc expr) "frac_chunk" 0)))
            [ expr3_1; expr3_2 ]
        in

        let* () =
          Rewriter.Logs.debug (fun printers m ->
              m "Lowering.rewrite_own_expr_4_arg:\n            expr3: %a" printers.pr_expr
                expr3)
        in

        Rewriter.return expr3
      in

      Expr.App (Own, [ expr1; expr2; expr3 ], expr_attr)
  | _ -> Rewriter.Expr.descend expr ~f:rewrite_own_expr_4_arg

let rec rewrite_new_fpu_stmt_heap_arg (stmt : Stmt.t) : Stmt.t Rewriter.t =
  let open Rewriter.Syntax in
  (* Logs.debug (fun m -> m "Lowering.rewrite_new_fpu_stmt_heap_arg: stmt: %a" Stmt.pr stmt); *)
  match stmt.stmt_desc with
  | Basic (New new_desc) ->
      let* new_args =
        Rewriter.List.map new_desc.new_args ~f:(fun (field_name, expr_optn) ->
            match expr_optn with
            | None -> Rewriter.return (field_name, expr_optn)
            | Some expr ->
                let* expr_typ = !Rewriter.expand_type_expr_ref (Expr.to_type expr) in

                let* field_elem_type =
                  let+ field_symbol = Rewriter.find_and_reify field_name in

                  match field_symbol with
                  | FieldDef f -> (
                      match f.field_type with
                      | App (Fld, [ tp_expr ], _) -> tp_expr
                      | _ ->
                          Error.type_error (Expr.to_loc expr) "Expected field identifier."
                      )
                  | _ -> Error.internal_error stmt.stmt_loc "expected a field_def"
                in

                let* field_elem_typ_expanded =
                  !Rewriter.expand_type_expr_ref field_elem_type
                in

                if Type.(expr_typ = field_elem_typ_expanded) then
                  Rewriter.return (field_name, expr_optn)
                else
                  let frac_mod_name =
                    match field_elem_type with
                    | App (Var qual_iden, _, _) -> QualIdent.pop qual_iden
                    | _ ->
                        Error.type_error (Expr.to_loc expr) "Expected field identifier."
                  in

                  let frac_type =
                    Type.mk_var
                      (QualIdent.append frac_mod_name
                         (Ident.make (Expr.to_loc expr) "T" 0))
                  in
                  let new_expr =
                    Expr.mk_app ~loc:(Expr.to_loc expr) ~typ:frac_type
                      (Expr.DataConstr
                         (QualIdent.append frac_mod_name
                            (Ident.make (Expr.to_loc expr) "frac_chunk" 0)))
                      [ expr; Expr.mk_real 1.0 ]
                  in

                  Rewriter.return (field_name, Some new_expr))
      in

      Rewriter.return { stmt with stmt_desc = Basic (New { new_desc with new_args }) }
  | Basic (Fpu fpu_desc) ->
      let compute_new_expr old_expr field_name =
        let loc = Expr.to_loc old_expr in
        let* expr_typ = !Rewriter.expand_type_expr_ref (Expr.to_type old_expr) in

        let* field_elem_type =
          let+ field_symbol = Rewriter.find_and_reify field_name in

          match field_symbol with
          | FieldDef f -> (
              match f.field_type with
              | App (Fld, [ tp_expr ], _) -> tp_expr
              | _ -> Error.type_error loc "Expected field identifier.")
          | _ -> Error.internal_error stmt.stmt_loc "expected a field_def"
        in

        let* field_elem_typ_expanded = !Rewriter.expand_type_expr_ref field_elem_type in

        if Type.(expr_typ = field_elem_typ_expanded) then Rewriter.return old_expr
        else
          let* field_type =
            let+ field_symbol = Rewriter.find_and_reify field_name in

            match field_symbol with
            | FieldDef f -> f.field_type
            | _ -> Error.internal_error stmt.stmt_loc "expected a field_def"
          in

          let frac_mod_name =
            match field_elem_type with
            | App (Var qual_iden, _, _) -> QualIdent.pop qual_iden
            | _ -> Error.type_error loc "Expected field identifier."
          in

          let frac_type =
            Type.mk_var (QualIdent.append frac_mod_name (Ident.make loc "T" 0))
          in
          let new_expr =
            Expr.mk_app ~loc ~typ:frac_type
              (Expr.DataConstr
                 (QualIdent.append frac_mod_name (Ident.make loc "frac_chunk" 0)))
              [ old_expr; Expr.mk_real 1.0 ]
          in

          Rewriter.return new_expr
      in

      let* fpu_old_val =
        match fpu_desc.fpu_old_val with
        | None -> Rewriter.return None
        | Some expr ->
            let+ new_expr = compute_new_expr expr fpu_desc.fpu_field in
            Some new_expr
      in

      let* fpu_new_val = compute_new_expr fpu_desc.fpu_new_val fpu_desc.fpu_field in

      let new_fpu_desc = { fpu_desc with fpu_old_val; fpu_new_val } in

      Rewriter.return { stmt with stmt_desc = Basic (Fpu new_fpu_desc) }
  | _ -> Rewriter.Stmt.descend stmt ~f:rewrite_new_fpu_stmt_heap_arg

(* Adds a lemma checking that two instances of a predicate or invariant held at
   the same time agree on their implicit parameters if they agree on the explicit
   ones. *)
let rewrite_add_predicate_validity_lemmas (c : Callable.t) : Callable.t Rewriter.t =
  let open Rewriter.Syntax in
  if is_free c.call_decl.call_decl_status then Rewriter.return c
  else
    match c.call_decl.call_decl_kind with
    | Pred | Invariant -> (
        match (c.call_decl.call_decl_returns, c.call_def) with
        | [], _ | _, FuncDef { func_body = None } -> Rewriter.return c
        | rets, FuncDef { func_body = Some body } ->
            let pred_valid_lemma_ident =
              Ident.fresh c.call_decl.call_decl_loc
                ("pred_valid$" ^ Ident.to_string c.call_decl.call_decl_name)
            in

            let formal_args, renaming_map1, renaming_map2, postconds =
              let renamings, explicit_args =
                List.fold_map c.call_decl.call_decl_formals
                  ~init:(Map.empty (module QualIdent))
                  ~f:(fun acc_renamings var_decl ->
                    let new_var_decl =
                      {
                        var_decl with
                        var_name =
                          Ident.fresh var_decl.var_loc var_decl.var_name.ident_name;
                      }
                    in
                    let new_var_expr = Expr.from_var_decl new_var_decl in

                    ( Map.add_exn acc_renamings
                        ~key:(QualIdent.from_ident var_decl.var_name)
                        ~data:new_var_expr,
                      new_var_decl ))
              in

              let renamings1, implicit_args1 =
                List.fold_map rets ~init:renamings ~f:(fun acc_renamings var_decl ->
                    let new_var_decl =
                      {
                        var_decl with
                        var_name =
                          Ident.fresh var_decl.var_loc var_decl.var_name.ident_name;
                      }
                    in
                    let new_var_expr = Expr.from_var_decl new_var_decl in

                    ( Map.add_exn acc_renamings
                        ~key:(QualIdent.from_ident var_decl.var_name)
                        ~data:new_var_expr,
                      new_var_decl ))
              in

              let renamings2, implicit_args2 =
                List.fold_map rets ~init:renamings ~f:(fun acc_renamings var_decl ->
                    let new_var_decl =
                      {
                        var_decl with
                        var_name =
                          Ident.fresh var_decl.var_loc var_decl.var_name.ident_name;
                      }
                    in
                    let new_var_expr = Expr.from_var_decl new_var_decl in

                    ( Map.add_exn acc_renamings
                        ~key:(QualIdent.from_ident var_decl.var_name)
                        ~data:new_var_expr,
                      new_var_decl ))
              in

              let postconds =
                List.map2_exn implicit_args1 implicit_args2
                  ~f:(fun implicit_arg1 implicit_arg2 ->
                    let spec_expr =
                      Expr.mk_eq ~loc:(Expr.to_loc body)
                        (Expr.from_var_decl implicit_arg1)
                        (Expr.from_var_decl implicit_arg2)
                    in
                    let error =
                      ( Error.Verification,
                        implicit_arg1.var_loc,
                        "Two instances held at the same time that agree on the explicit \
                         parameters may disagree on this implicit parameter" )
                    in
                    Stmt.mk_spec ~spec_error:[ (fun _ _ -> error) ] spec_expr)
              in

              ( explicit_args @ implicit_args1 @ implicit_args2,
                renamings1,
                renamings2,
                postconds )
            in

            (*let postcond =
            let error = (Error.Verification, 
             (Expr.mk_bool ~loc:(Expr.to_loc body) false)
          in*)
            let call_decl =
              {
                Callable.call_decl_kind = Lemma;
                call_decl_name = pred_valid_lemma_ident;
                call_decl_formals = formal_args;
                call_decl_returns = [];
                call_decl_locals = [];
                call_decl_precond = [];
                call_decl_postcond = postconds;
                call_decl_contract_ext = [];
                call_decl_status = NotFree;
                call_decl_is_auto = false;
                call_decl_is_inline = false;
                (* This callable is created in `rewrites_phase_3`, after
                 `Masks.compute_masks`/atomicity analysis have already run, so
                 it never goes through the mask fixpoint and `call_decl_needs_mask`
                 would otherwise be stuck at `None` forever. Safe to seed it
                 as `Some []` directly: the body below is just two `inhale`s
                 -- structurally impossible to unfold an invariant, so it can
                 never have a real mask requirement. *)
                call_decl_needs_mask = Some [];
                call_decl_grants_mask = Some [];
                call_decl_opens = None;
                call_decl_loc = c.call_decl.call_decl_loc;
                call_decl_loc_params = [];
              }
            in

            let* pred_qual_ident = Rewriter.current_scope_id in

            let call_body =
              Stmt.mk_block_stmt ~loc:c.call_decl.call_decl_loc
                [
                  Stmt.mk_inhale_expr ~loc:c.call_decl.call_decl_loc
                    ~spec_source:(pred_qual_ident, 0)
                    (Expr.alpha_renaming body renaming_map1);
                  Stmt.mk_inhale_expr ~loc:c.call_decl.call_decl_loc
                    ~spec_source:(pred_qual_ident, 0)
                    (Expr.alpha_renaming body renaming_map2);
                ]
            in

            let call_def =
              Module.CallDef
                Callable.{ call_decl; call_def = ProcDef { proc_body = Some call_body } }
            in

            let* _ =
              Rewriter.introduce_typecheck_symbol ~loc:c.call_decl.call_decl_loc
                ~f:Typing.process_symbol call_def
            in

            Rewriter.return c
        | _, ProcDef _ ->
            Error.internal_error c.call_decl.call_decl_loc
              "Expected a function definition for a predicate")
    | _ -> Rewriter.return c

let rewrite_introduce_heaps (c : Callable.t) : Callable.t Rewriter.t =
  let open Rewriter.Syntax in
  Logs.debug (fun m ->
      m "Lowering.rewrite_introduce_heaps: Introducing heaps in callable: %a" Ident.pr
        c.call_decl.call_decl_name);
  match c.call_def with
  | FuncDef _ -> Rewriter.return c
  | ProcDef { proc_body = None } -> Rewriter.return c
  | ProcDef { proc_body = Some body } ->
      let* preds_list = ProgUtils.stmt_preds_mentioned body in
      let* ext_hooks = Rewriter.current_ext_hooks in
      let fields_list =
        Stmt.make_stmt_fields_accessed
          ~basic_stmt_ext_fields_accessed:ext_hooks.basic_stmt_ext_fields_accessed
          ~stmt_ext_fields_accessed:ext_hooks.stmt_ext_fields_accessed body
      in
      let au_preds_list = Set.to_list (Stmt.stmt_au_preds_referenced body) in

      Logs.debug (fun m ->
          m "Lowering.rewrite_introduce_heaps: Predicates mentioned in the body");

      let* body =
        HeapsExplicitTrnsl.introduce_heaps_in_stmts ~loc:c.call_decl.call_decl_loc
          ~fields_list ~preds_list ~au_preds_list body
      in

      Rewriter.return { c with call_def = ProcDef { proc_body = Some body } }

let rec rewrite_ssa_stmts (s : Stmt.t) : (Stmt.t, var_decl ident_map) Rewriter.t_ext =
  let open Rewriter.Syntax in
  let* var_map = Rewriter.current_user_state in
  let subst_map = Map.map var_map ~f:(fun var_decl -> Expr.from_var_decl var_decl) in
  let subst_map =
    (Map.map_keys_exn (module QualIdent)) subst_map ~f:(fun ident ->
        QualIdent.from_ident ident)
  in

  match s.stmt_desc with
  | Basic basic_stmt -> (
      match basic_stmt with
      | Spec (spec_kind, spec) ->
          let spec_form = Expr.alpha_renaming spec.spec_form subst_map in

          Rewriter.return
            Stmt.{ s with stmt_desc = Basic (Spec (spec_kind, { spec with spec_form })) }
      | Assign assign_stmt ->
          let assign_rhs = Expr.alpha_renaming assign_stmt.assign_rhs subst_map in
          let* assign_lhs =
            if assign_stmt.assign_is_init then Rewriter.return assign_stmt.assign_lhs
            else
              Rewriter.List.map assign_stmt.assign_lhs ~f:(fun qual_ident ->
                  let* var_map = Rewriter.current_user_state in

                  let local_var = QualIdent.to_ident qual_ident in

                  let* () =
                    Rewriter.Logs.debug (fun printers m ->
                        m
                          "Lowering.rewrite_ssa_stmts: Assigning to local variable %a; \
                           for stmt %a"
                          Ident.pr local_var printers.pr_stmt s)
                  in
                  let old_var_decl = Map.find_exn var_map local_var in
                  let new_var_decl =
                    Type.
                      {
                        old_var_decl with
                        var_name =
                          Ident.fresh old_var_decl.var_loc
                            old_var_decl.var_name.ident_name;
                      }
                  in

                  let* _ =
                    Rewriter.introduce_symbol
                      (VarDef
                         {
                           var_decl = new_var_decl;
                           var_init = None;
                           var_is_free = NotFree;
                         })
                  in

                  let var_map = Map.set var_map ~key:local_var ~data:new_var_decl in

                  let+ _ = Rewriter.set_user_state var_map in

                  QualIdent.from_ident new_var_decl.var_name)
          in

          Rewriter.return
            Stmt.
              {
                s with
                stmt_desc = Basic (Assign { assign_stmt with assign_lhs; assign_rhs });
              }
      | Havoc hvc ->
          if not (QualIdent.is_local hvc.havoc_var) then assert false
          else if hvc.havoc_is_init then Rewriter.return (Stmt.mk_skip ~loc:s.stmt_loc)
          else
            let local_var = QualIdent.to_ident hvc.havoc_var in

            Logs.debug (fun m ->
                m "Lowering.rewrite_ssa_stmts: Havocing local variable %a" Ident.pr
                  local_var);
            let old_var_decl = Map.find_exn var_map local_var in
            let new_var_decl =
              {
                old_var_decl with
                var_name =
                  Ident.fresh old_var_decl.var_loc old_var_decl.var_name.ident_name;
              }
            in

            let* _ =
              Rewriter.introduce_symbol
                (VarDef
                   { var_decl = new_var_decl; var_init = None; var_is_free = NotFree })
            in

            let var_map = Map.set var_map ~key:local_var ~data:new_var_decl in

            let+ _ = Rewriter.set_user_state var_map in

            Stmt.mk_block_stmt ~loc:s.stmt_loc []
      | Bind bind_stmt ->
          let* bind_lhs =
            Rewriter.List.map bind_stmt.bind_lhs ~f:(fun qual_ident ->
                let* var_map = Rewriter.current_user_state in

                let local_var = QualIdent.unqualify qual_ident in

                let old_var_decl = Map.find_exn var_map local_var in
                let new_var_decl =
                  Type.
                    {
                      old_var_decl with
                      var_name =
                        Ident.fresh old_var_decl.var_loc old_var_decl.var_name.ident_name;
                    }
                in

                let* _ =
                  Rewriter.introduce_symbol
                    (VarDef
                       { var_decl = new_var_decl; var_init = None; var_is_free = NotFree })
                in

                let var_map = Map.set var_map ~key:local_var ~data:new_var_decl in

                let+ _ = Rewriter.set_user_state var_map in

                QualIdent.from_ident new_var_decl.var_name)
          in

          let* var_map = Rewriter.current_user_state in
          let subst_map =
            Map.map var_map ~f:(fun var_decl -> Expr.from_var_decl var_decl)
          in
          let subst_map =
            (Map.map_keys_exn (module QualIdent)) subst_map ~f:(fun ident ->
                QualIdent.from_ident ident)
          in

          let spec_form = Expr.alpha_renaming bind_stmt.bind_rhs.spec_form subst_map in
          let bind_rhs = { bind_stmt.bind_rhs with spec_form } in

          Rewriter.return Stmt.{ s with stmt_desc = Basic (Bind { bind_lhs; bind_rhs }) }
      | _ ->
          let* () =
            Rewriter.Logs.debug (fun printers m ->
                m "Lowering.rewrite_ssa_stmts: Skipping statement %a" printers.pr_stmt s)
          in
          assert false)
  | Block block_stmt ->
      let+ block_body = Rewriter.List.map block_stmt.block_body ~f:rewrite_ssa_stmts in

      Stmt.mk_block_stmt ~kind:block_stmt.block_kind ~loc:s.stmt_loc block_body
      (* { s with stmt_desc = Block { block_stmt with block_body; } } *)
  | Cond cond_stmt when not cond_stmt.cond_if_assumes_false ->
      let cond_test =
        Option.map ~f:(fun test -> Expr.alpha_renaming test subst_map) cond_stmt.cond_test
      in

      let* cond_then = rewrite_ssa_stmts cond_stmt.cond_then in

      let* cond_then_map = Rewriter.current_user_state in

      let* _ = Rewriter.set_user_state var_map in
      let* cond_else = rewrite_ssa_stmts cond_stmt.cond_else in

      let* cond_else_map = Rewriter.current_user_state in

      let updated_vals =
        Map.fold2 cond_then_map cond_else_map ~init:[] ~f:(fun ~key ~data acc ->
            match data with
            | `Both (then_var_decl, else_var_decl) ->
                if Ident.(Type.(then_var_decl.var_name) = Type.(else_var_decl.var_name))
                then acc
                else key :: acc
            | `Left _ | `Right _ ->
                Error.error s.stmt_loc
                  "Mismatched variable declarations in then and else branches.")
      in

      let* new_var_map =
        Rewriter.List.fold_left updated_vals ~init:var_map ~f:(fun map var ->
            let old_var_decl = Map.find_exn var_map var in
            let new_var_decl =
              {
                old_var_decl with
                var_name =
                  Ident.fresh old_var_decl.var_loc old_var_decl.var_name.ident_name;
              }
            in

            let+ _ =
              Rewriter.introduce_symbol
                (VarDef
                   { var_decl = new_var_decl; var_init = None; var_is_free = NotFree })
            in

            Map.set map ~key:var ~data:new_var_decl)
      in

      let cond_then_assigns =
        List.map updated_vals ~f:(fun var ->
            let old_var_decl = Map.find_exn cond_then_map var in
            let new_var_decl = Map.find_exn new_var_map var in

            Stmt.mk_assign ~loc:s.stmt_loc
              [ QualIdent.from_ident new_var_decl.var_name ]
              (Expr.from_var_decl old_var_decl))
      in

      let cond_then =
        Stmt.mk_block_stmt ~loc:s.stmt_loc (cond_then :: cond_then_assigns)
      in

      let cond_else_assigns =
        List.map updated_vals ~f:(fun var ->
            let old_var_decl = Map.find_exn cond_else_map var in
            let new_var_decl = Map.find_exn new_var_map var in

            Stmt.mk_assign ~loc:s.stmt_loc
              [ QualIdent.from_ident new_var_decl.var_name ]
              (Expr.from_var_decl old_var_decl))
      in

      let cond_else =
        Stmt.mk_block_stmt ~loc:s.stmt_loc (cond_else :: cond_else_assigns)
      in

      let+ _ = Rewriter.set_user_state new_var_map in

      Stmt.
        {
          s with
          stmt_desc =
            Cond { cond_test; cond_then; cond_else; cond_if_assumes_false = false };
        }
  | Cond cond_stmt ->
      assert cond_stmt.cond_if_assumes_false;
      assert (
        Poly.(
          cond_stmt.cond_else.stmt_desc = Block { block_kind = Regular; block_body = [] }));

      let* orig_map = Rewriter.current_user_state in

      let cond_test =
        Option.map ~f:(fun test -> Expr.alpha_renaming test subst_map) cond_stmt.cond_test
      in

      let* cond_then = rewrite_ssa_stmts cond_stmt.cond_then in
      let* cond_else = rewrite_ssa_stmts cond_stmt.cond_else in

      let* _ = Rewriter.set_user_state orig_map in

      Rewriter.return
        Stmt.
          {
            s with
            stmt_desc =
              Cond { cond_test; cond_then; cond_else; cond_if_assumes_false = true };
          }
  | Loop loop_stmt -> assert false
  | StmtExt _ -> assert false

let rewrite_ssa_transform (c : Callable.t) :
    (Callable.t, var_decl ident_map) Rewriter.t_ext =
  let open Rewriter.Syntax in
  match c.call_def with
  | FuncDef _ | ProcDef { proc_body = None } -> Rewriter.return c
  | ProcDef { proc_body = Some body } ->
      let* () =
        Rewriter.Logs.debug (fun printers m ->
            m "rewrite_ssa_transform: init_map: %a"
              (Util.Print.pr_list_comma printers.pr_type_var_decl)
              (c.call_decl.call_decl_formals @ c.call_decl.call_decl_returns
             @ c.call_decl.call_decl_locals))
      in

      let init_map =
        List.fold
          (c.call_decl.call_decl_formals @ c.call_decl.call_decl_returns
         @ c.call_decl.call_decl_locals)
          ~init:(Map.empty (module Ident))
          ~f:(fun map var_decl -> Map.add_exn map ~key:var_decl.var_name ~data:var_decl)
      in

      let* _ = Rewriter.set_user_state init_map in

      let* () =
        Rewriter.Logs.debug (fun printers m ->
            m "Lowering.rewrite_ssa_transform: Starting rewrites on callable %a"
              printers.pr_callable c)
      in

      let+ body = rewrite_ssa_stmts body in

      { c with call_def = ProcDef { proc_body = Some body } }

let rec rewrite_assign_stmts (s : Stmt.t) : Stmt.t Rewriter.t =
  let open Rewriter.Syntax in
  let* () =
    Rewriter.Logs.debug (fun printers m ->
        m "Lowering.rewrite_assign_stmts: Starting rewrites on statement %a"
          printers.pr_stmt s)
  in

  match s.stmt_desc with
  | Basic (Assign assign_stmt) ->
      let+ assign_lhs =
        Rewriter.List.map assign_stmt.assign_lhs ~f:(fun qual_ident ->
            let* qual_ident, symbol = Rewriter.resolve_and_find qual_ident in
            let+ symbol = Rewriter.Symbol.reify symbol in
            match symbol with
            | VarDef { var_decl; _ } -> Expr.mk_var ~typ:var_decl.var_type qual_ident
            | _ -> assert false)
      in

      let assume_stmt =
        Stmt.mk_assume_expr ~loc:s.stmt_loc
          (Expr.mk_eq (Expr.mk_tuple assign_lhs) assign_stmt.assign_rhs)
      in

      assume_stmt
  | _ -> let* s = Rewriter.Stmt.descend s ~f:rewrite_assign_stmts in

         Rewriter.return s

let lower (m : Module.t) : (Module.t * CallGraph.Graph.t) Rewriter.t =
  let open Rewriter.Syntax in
  Logs.debug (fun m1 ->
      m1 "Lowering.lower: Starting rewrite_fold_unfold_stmts on module %a" Ident.pr
        m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_stmts ~f:rewrite_fold_unfold_stmts m in

  let* tbl = Rewriter.get_table in
  let lemma_calls = CallGraph.lemma_calls tbl m in

  Logs.debug (fun m1 ->
      m1 "Lowering.lower: Starting rewrite_call_stmts on module %a" Ident.pr
        m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_stmts ~f:rewrite_call_stmts m in

  Logs.debug (fun m1 ->
      m1 "Lowering.lower: Starting rewrite_ret_stmts on module %a" Ident.pr
        m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_stmts ~f:rewrite_ret_stmts m in

  Logs.debug (fun m1 ->
      m1 "Lowering.lower: Starting rewrite_frac_field_types on module %a" Ident.pr
        m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rec_rewrite_symbols ~f:rewrite_frac_field_types m in

  let* () =
    Rewriter.Logs.debug (fun _ m1 ->
        m1 "Lowering.lower: Starting canonicalize_symbols on module %a" Ident.pr
          m.mod_decl.mod_decl_name)
  in
  let* m = Rewriter.Module.rewrite_expressions ~f:canonicalize_symbols m in

  Logs.debug (fun m1 ->
      m1 "Lowering.lower: Starting rewrite_own_expr_4_arg on module %a" Ident.pr
        m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_expressions ~f:rewrite_own_expr_4_arg m in

  Logs.debug (fun m1 ->
      m1 "Lowering.lower: Starting rewrite_new_fpu_stmt_heap_arg on module %a" Ident.pr
        m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_stmts ~f:rewrite_new_fpu_stmt_heap_arg m in

  Logs.debug (fun m1 ->
      m1 "Lowering.lower: Starting rewrite_new_stmts on module %a" Ident.pr
        m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_stmts ~f:rewrite_new_stmts m in

  Logs.debug (fun m1 ->
      m1 "Lowering.lower: Starting rewrite_add_predicate_validity_lemmas on module %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_callables ~f:rewrite_add_predicate_validity_lemmas m in

  Logs.debug (fun m1 ->
      m1 "Lowering.lower: Starting rewrite_callable_pre_post_conds on module %a" Ident.pr
        m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_callables ~f:rewrite_callable_pre_post_conds m in

  Logs.debug (fun m1 ->
      m1 "Lowering.lower: Starting rewrite_add_pred_implicit_args on module %a" Ident.pr
        m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_expressions ~f:rewrite_add_pred_implicit_args m in

  Logs.debug (fun m1 ->
      m1 "Lowering.lower: Starting rewrite_add_field_utils on module %a" Ident.pr
        m.mod_decl.mod_decl_name);
  let* m =
    Rewriter.Module.rec_rewrite_symbols ~f:HeapsExplicitTrnsl.rewrite_add_field_utils m
  in

  Logs.debug (fun m1 ->
      m1 "Lowering.lower: Starting rewrite_add_pred_utils on module %a" Ident.pr
        m.mod_decl.mod_decl_name);
  let* m =
    Rewriter.Module.rewrite_callables ~f:HeapsExplicitTrnsl.rewrite_add_pred_utils m
  in

  Logs.debug (fun m1 ->
      m1 "Lowering.lower: Starting rewrite_add_atomics_utils on module %a" Ident.pr
        m.mod_decl.mod_decl_name);
  let* m =
    Rewriter.Module.rewrite_callables ~f:HeapsExplicitTrnsl.rewrite_add_atomics_utils m
  in

  Logs.debug (fun m1 ->
      m1 "Lowering.lower: Starting rewriter_skolemize_inhale_stmts on module %a" Ident.pr
        m.mod_decl.mod_decl_name);
  let* m =
    Rewriter.Module.rewrite_stmts
      ~f:HeapsExplicitTrnsl.TrnslInhale.rewriter_skolemize_inhale_stmts m
  in

  Logs.debug (fun m1 ->
      m1
        "Lowering.lower: Starting rewriter_user_annot_elim_exists_from_exhales on module \
         %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m =
    Rewriter.eval_with_user_state ~init:None
      (Rewriter.Module.rewrite_stmts
         ~f:HeapsExplicitTrnsl.TrnslExhale.rewriter_user_annot_elim_exists_from_exhales m)
  in

  Logs.debug (fun m1 ->
      m1 "Lowering.lower: Starting rewrite_introduce_heaps on module %a" Ident.pr
        m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_callables ~f:rewrite_introduce_heaps m in

  Logs.debug (fun m1 ->
      m1 "Lowering.lower: Starting rewriter_eliminate_binds_for_inhale on module %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m =
    Rewriter.eval_with_user_state ~init:None
      (Rewriter.Module.rewrite_stmts
         ~f:HeapsExplicitTrnsl.TrnslInhale.rewriter_eliminate_binds_for_inhale m)
  in

  Logs.debug (fun m1 ->
      m1 "Lowering.lower: Starting rewrite_fpu on module %a" Ident.pr
        m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_stmts ~f:HeapsExplicitTrnsl.rewrite_fpu m in

  Logs.debug (fun m1 ->
      m1 "Lowering.lower: Starting rewrite_binds on module %a" Ident.pr
        m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_stmts ~f:HeapsExplicitTrnsl.rewrite_binds m in

  Logs.debug (fun m1 ->
      m1 "Lowering.lower: Starting rewriter_skolemize_assume_stmts on module %a" Ident.pr
        m.mod_decl.mod_decl_name);
  let* m =
    Rewriter.Module.rewrite_stmts
      ~f:HeapsExplicitTrnsl.TrnslInhale.rewriter_skolemize_assume_stmts m
  in

  Logs.debug (fun m1 ->
      m1
        "Lowering.lower: Starting rewriter_find_witness_elim_exists_from_exhale on \
         module %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m =
    Rewriter.Module.rewrite_stmts
      ~f:HeapsExplicitTrnsl.TrnslExhale.rewriter_find_witness_elim_exists_from_exhale m
  in

  Logs.debug (fun m1 ->
      m1 "Lowering.lower: Starting rewrite_make_heaps_explicit on module %a" Ident.pr
        m.mod_decl.mod_decl_name);
  let* m =
    Rewriter.Module.rewrite_stmts ~f:HeapsExplicitTrnsl.rewrite_make_heaps_explicit m
  in

  Logs.debug (fun m1 ->
      m1 "Lowering.lower: Starting rewrite_expand_types on module %a" Ident.pr
        m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_types ~f:rewrite_expand_types m in

  let* () =
    Rewriter.Logs.debug (fun printers m1 ->
        m1 "Lowering.lower: Starting rewrite_ssa_transform on module %a: %a" Ident.pr
          m.mod_decl.mod_decl_name printers.pr_module m)
  in
  let* m =
    Rewriter.eval_with_user_state
      ~init:(Map.empty (module Ident))
      (Rewriter.Module.rewrite_callables ~f:rewrite_ssa_transform m)
  in

  Logs.debug (fun m1 ->
      m1 "Lowering.lower: Starting rewrite_assign_stmts on module %a" Ident.pr
        m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_stmts ~f:rewrite_assign_stmts m in

  let* tbl = Rewriter.get_table in

  (* Logs.debug (fun m -> m "Lowering.lower: SymbolTbl Symbols: \n%a\n" (Util.Print.pr_list_comma (fun ppf (k,v) -> Stdlib.Format.fprintf ppf "%a -> %a" QualIdent.pr k Module.pr_symbol v)) (Map.to_alist (Map.filter_keys tbl.tbl_symbols ~f:(fun k -> Poly.((QualIdent.to_string k) = "$Program.pr"))))); *)
  Rewriter.return (m, lemma_calls)

(** Lowers the front end's output for [m] to what the SMT encoding is generated from:
    calls, folds and returns become inhales and exhales, fields resource algebras, heaps
    explicit, and assignments SSA. Returns the module together with its lemma call graph
    (see [CallGraph.lemma_calls]). Every compilation unit goes through the front end
    before any is lowered (see [Rewrites.process_module_front]). *)
let lower_module ?(tbl = SymbolTbl.create ()) ?ext_hooks ?cli_config (m : Module.t) =
  assert (SymbolTbl.curr_is_root tbl);
  let tbl, (m, lemma_calls) = Rewriter.eval ?ext_hooks ?cli_config (lower m) tbl in
  (tbl, m, lemma_calls)
