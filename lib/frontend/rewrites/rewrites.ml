open Base
open Ast
open Util
open Frontend

let rec rewrite_stmt_error_msg call_id (stmt : Stmt.t) : Stmt.t Rewriter.t =
  match stmt.stmt_desc with
  | Basic (Spec (((Assert | Exhale) as kind), spec)) ->
      let error =
        ( Error.Verification,
          Expr.to_loc spec.spec_form,
          match kind with
          | Assert -> "This assertion may be violated"
          | _ -> "Possibly insufficient permissions to exhale this assertion" )
      in
      let spec_error = [ Stmt.mk_const_spec_error error ] in
      Rewriter.return
        { stmt with stmt_desc = Basic (Spec (kind, { spec with spec_error })) }
  | Loop loop_desc ->
      let loop_contract =
        List.map loop_desc.loop_contract ~f:(fun spec ->
            let error callee =
              ( Error.Verification,
                Expr.to_loc spec.spec_form,
                if Ident.(QualIdent.unqualify callee <> call_id) then
                  "This loop invariant may not hold upon loop entry"
                else "This loop invariant may not be maintained" )
            in
            { spec with spec_error = [ error ] })
      in
      let stmt =
        { stmt with stmt_desc = Loop { loop_desc with loop_contract } }
      in
      Rewriter.Stmt.descend ~f:(rewrite_stmt_error_msg call_id) stmt
  | _ -> Rewriter.Stmt.descend ~f:(rewrite_stmt_error_msg call_id) stmt

let rewrite_callable_error_msg (call : Callable.t) : Callable.t Rewriter.t =
  let open Rewriter.Syntax in
  let call_decl = call |> Callable.to_decl in
  let call_decl_postcond =
    List.map call_decl.call_decl_postcond ~f:(fun spec ->
        let error =
          ( Error.RelatedLoc,
            spec.spec_form |> Expr.to_loc,
            "This is the postcondition that may not hold" )
        in
        { spec with spec_error = [ Stmt.mk_const_spec_error error ] })
  in
  let call_decl_precond =
    List.map call_decl.call_decl_precond ~f:(fun spec ->
        let error =
          ( Error.RelatedLoc,
            spec.spec_form |> Expr.to_loc,
            "This is the precondition that may not hold" )
        in
        { spec with spec_error = [ Stmt.mk_const_spec_error error ] })
  in
  let call_decl = { call_decl with call_decl_postcond; call_decl_precond } in
  let+ call_def =
    match call.call_def with
    | ProcDef { proc_body = Some stmt } ->
        let+ body = rewrite_stmt_error_msg call_decl.call_decl_name stmt in
        Callable.ProcDef { proc_body = Some body }
    | _ -> Rewriter.return call.call_def
  in
  Callable.{ call_decl; call_def }

let rec rewrite_expand_types (tp_expr : type_expr) : type_expr Rewriter.t =
  Typing.ProcessTypeExpr.expand_type_expr tp_expr

let rec rewrite_compr_expr (expr : expr) : expr Rewriter.t =
  let open Rewriter.Syntax in
  match expr with
  | Binder (Compr, v_l, trgs, inner_expr, _expr_attr) ->
      let* _ = Rewriter.add_locals v_l
      and* inner_expr = rewrite_compr_expr inner_expr in

      let compr_fn_ident = Ident.fresh (Expr.to_loc expr) "compr" in

      let free_vars = Expr.signature inner_expr in
      let free_vars =
        Map.filter_keys free_vars ~f:(fun qual_ident ->
            not
              (List.exists v_l ~f:(fun v_l ->
                   Poly.(QualIdent.from_ident v_l.var_name = qual_ident))))
      in

      let formal_var_decls, actual_arg_exprs =
        Map.fold free_vars ~init:([], [])
          ~f:(fun ~key ~data (formals, actuals) ->
            if QualIdent.is_qualified key then (formals, actuals)
            else
              ( {
                  Type.var_name = QualIdent.unqualify key;
                  var_loc = Expr.to_loc inner_expr;
                  var_type = data;
                  var_const = true;
                  var_ghost = false;
                  var_implicit = false;
                }
                :: formals,
                Expr.mk_var ~loc:(Expr.to_loc inner_expr) ~typ:data key
                :: actuals ))
      in

      let ret_var_decl =
        {
          Type.var_name = Ident.fresh (Expr.to_loc expr) "ret";
          var_loc = Expr.to_loc expr;
          var_type = Expr.to_type expr;
          var_const = false;
          var_ghost = false;
          var_implicit = false;
        }
      in

      let ret_typ = Expr.to_type expr in

      let postcond =
        let spec_form =
          if Type.is_set ret_typ then
            let var_decl = List.hd_exn v_l in

            Expr.mk_binder ~typ:Type.bool Forall [ var_decl ]
              (Expr.mk_and
                 [
                   Expr.mk_app ~typ:Type.bool Impl
                     [
                       inner_expr;
                       Expr.mk_app ~typ:Type.bool Elem
                         [
                           Expr.from_var_decl var_decl;
                           Expr.from_var_decl ret_var_decl;
                         ];
                     ];
                   Expr.mk_app ~typ:Type.bool Impl
                     [
                       Expr.mk_app ~typ:Type.bool Elem
                         [
                           Expr.from_var_decl var_decl;
                           Expr.from_var_decl ret_var_decl;
                         ];
                       inner_expr;
                     ];
                 ])
          else
            (* Type.is_map ret_typ *)
            let var_decl = List.hd_exn v_l in

            Expr.mk_binder ~typ:Type.bool Forall [ var_decl ]
              (Expr.mk_app ~typ:Type.bool Eq
                 [
                   inner_expr;
                   Expr.mk_app ~typ:(Type.map_codom ret_typ) MapLookUp
                     [
                       Expr.from_var_decl ret_var_decl;
                       Expr.from_var_decl var_decl;
                     ];
                 ])
        in

        Stmt.mk_spec spec_form
      in

      let call_decl =
        {
          Callable.call_decl_kind = Func;
          call_decl_name = compr_fn_ident;
          call_decl_formals = formal_var_decls;
          call_decl_returns = [ ret_var_decl ];
          call_decl_locals = [];
          call_decl_precond = [];
          call_decl_postcond = [ postcond ];
          call_decl_is_free = true;
          call_decl_is_auto = false;
          call_decl_mask = None;
          call_decl_loc = Expr.to_loc expr;
        }
      in

      let* current_module_name = Rewriter.current_module_name in
      let compr_fn_qual_ident =
        QualIdent.append current_module_name compr_fn_ident
      in
      let compr_fn_def =
        Module.CallDef
          Callable.{ call_decl; call_def = FuncDef { func_body = None } }
      in

      Logs.debug (fun m ->
          m "Rewrites.rewrite_compr_expr: compr_fn: %a" Symbol.pr compr_fn_def);

      let new_expr =
        Expr.mk_app ~typ:ret_typ ~loc:(Expr.to_loc expr)
          (Expr.Var compr_fn_qual_ident) actual_arg_exprs
      in

      (* TODO: Change Rewriter.introduce_symbol to Rewriter.introduce_typecheck_symbol *)
      let+ _ = Rewriter.introduce_symbol compr_fn_def in
      new_expr
  | _ -> Rewriter.Expr.descend expr ~f:rewrite_compr_expr

let rec rewrite_set_diff_expr (expr : expr) : expr Rewriter.t =
  let open Rewriter.Syntax in
  match expr with
  | App (Diff, [ expr1; expr2 ], _expr_attr) ->
      Logs.debug (fun m ->
          m "Rewrites.rewrite_set_diff_expr: expr: %a" Expr.pr expr);

      let set_element_type = Type.set_elem (Expr.to_type expr1) in
      let typ_string =
        Rewriter.ProgUtils.serialize (Type.to_string set_element_type)
      in

      let set_diff_fn_ident =
        Ident.fresh (Expr.to_loc expr)
          (Stdlib.Format.asprintf "set_diff$%s" typ_string)
      in

      (* let free_vars = Expr.signature inner_expr in *)
      let var_decl1 =
        {
          Type.var_name = Ident.fresh (Expr.to_loc expr) "a";
          var_loc = Expr.to_loc expr;
          var_type = Expr.to_type expr1;
          var_const = true;
          var_ghost = false;
          var_implicit = false;
        }
      in

      let var_decl2 =
        {
          Type.var_name = Ident.fresh (Expr.to_loc expr) "b";
          var_loc = Expr.to_loc expr;
          var_type = Expr.to_type expr1;
          var_const = true;
          var_ghost = false;
          var_implicit = false;
        }
      in

      let formal_var_decls, actual_arg_exprs =
        ([ var_decl1; var_decl2 ], [ expr1; expr2 ])
      in

      let ret_var_decl =
        {
          Type.var_name = Ident.fresh (Expr.to_loc expr) "ret";
          var_loc = Expr.to_loc expr;
          var_type = Expr.to_type expr;
          var_const = false;
          var_ghost = false;
          var_implicit = false;
        }
      in

      let ret_typ = Expr.to_type expr in

      let postcond =
        let spec_form =
          let var_decl =
            {
              Type.var_name = Ident.fresh (Expr.to_loc expr) "x";
              var_loc = Expr.to_loc expr;
              var_type = set_element_type;
              var_const = true;
              var_ghost = false;
              var_implicit = false;
            }
          in

          Expr.mk_binder ~typ:Type.bool Forall [ var_decl ]
            ((* forall x :: *)
             Expr.mk_and
               [
                 Expr.mk_app ~typ:Type.bool Impl
                   [
                     (*    x \in a && !(x \in b)   ==>    x \in ret  *)
                     Expr.mk_and
                       [
                         Expr.mk_app ~typ:Type.bool Elem
                           [
                             Expr.from_var_decl var_decl;
                             Expr.from_var_decl var_decl1;
                           ];
                         Expr.mk_not
                           (Expr.mk_app ~typ:Type.bool Elem
                              [
                                Expr.from_var_decl var_decl;
                                Expr.from_var_decl var_decl2;
                              ]);
                       ];
                     Expr.mk_app ~typ:Type.bool Elem
                       [
                         Expr.from_var_decl var_decl;
                         Expr.from_var_decl ret_var_decl;
                       ];
                   ];
                 Expr.mk_app ~typ:Type.bool Impl
                   [
                     (*    x \in ret    ==>    x \in a && !(x \in b)  *)
                     Expr.mk_app ~typ:Type.bool Elem
                       [
                         Expr.from_var_decl var_decl;
                         Expr.from_var_decl ret_var_decl;
                       ];
                     Expr.mk_and
                       [
                         Expr.mk_app ~typ:Type.bool Elem
                           [
                             Expr.from_var_decl var_decl;
                             Expr.from_var_decl var_decl1;
                           ];
                         Expr.mk_not
                           (Expr.mk_app ~typ:Type.bool Elem
                              [
                                Expr.from_var_decl var_decl;
                                Expr.from_var_decl var_decl2;
                              ]);
                       ];
                   ];
               ])
        in

        Stmt.mk_spec spec_form
      in

      let call_decl =
        {
          Callable.call_decl_kind = Func;
          call_decl_name = set_diff_fn_ident;
          call_decl_formals = formal_var_decls;
          call_decl_returns = [ ret_var_decl ];
          call_decl_locals = [];
          call_decl_precond = [];
          call_decl_postcond = [ postcond ];
          call_decl_is_free = true;
          call_decl_is_auto = false;
          call_decl_mask = None;
          call_decl_loc = Expr.to_loc expr;
        }
      in

      let* current_module_name = Rewriter.current_module_name in

      let set_diff_fn_qual_ident =
        QualIdent.append current_module_name set_diff_fn_ident
      in
      let set_diff_fn_def =
        Module.CallDef
          Callable.{ call_decl; call_def = FuncDef { func_body = None } }
      in

      let new_expr =
        Expr.mk_app ~typ:ret_typ ~loc:(Expr.to_loc expr)
          (Expr.Var set_diff_fn_qual_ident) actual_arg_exprs
      in

      (* TODO: Change Rewriter.introduce_symbol to Rewriter.introduce_typecheck_symbol *)
      let+ _ =
        Rewriter.introduce_typecheck_symbol ~loc:(Expr.to_loc expr)
          ~f:Typing.process_symbol set_diff_fn_def
      in
      new_expr
  | _ -> Rewriter.Expr.descend expr ~f:rewrite_set_diff_expr

let rewrite_compr_modules (tbl : SymbolTbl.t) (m : Module.t) =
  Rewriter.eval
    (Rewriter.Module.rewrite_expressions ~f:rewrite_compr_expr m)
    tbl

(** Rewrites loops into recursive function calls. For example, if we have the following while loop:
  ```
    proc p() {
      ...
      while(c)
        inv i
      {
        x = y + z
      }
      ...
    }
  ```

  Then we rewrite it into the following, by defining a recursive function:
  ```
    proc p() {
      ...
      x = p_loop(x, y, z);
      ...
    }

    proc p_loop(x1: Int, y1: Int, z1: Int)
      returns x2
      requires i[x1\x, y1\y, z1\z]
      ensures i[x2\x, y1\y, z1\z]
      ensures !c[x2\x, y1\y, z1\z]
    {
      x2 := x1
      
      if(c[x1\x, y1\y, z1\z]) {
        x1 := y1 + z1;
        
        x2 := p_loop(x1, y1, z1);
      } else { 
      }

      return x2
    }
  ```
*)
let rec rewrite_loops (stmt : Stmt.t) : Stmt.t Rewriter.t =
  let open Rewriter.Syntax in
  match stmt.stmt_desc with
  | Loop loop ->
      let loc = Stmt.to_loc stmt in
      Logs.debug (fun m -> m "Rewrites.rewrite_loops: loop: %a" Stmt.pr stmt);

      let* ( loop_arg_var_decls,
             loop_arg_renaming_map,
             loop_arg_renaming_qual_ident_map,
             curr_loop_arg_var_decls ) =
        (* Local variables accessed from loop body become arguments for loop procedure *)
        let curr_loop_args =
          Set.union
            (Stmt.local_vars_accessed loop.loop_postbody)
            (Expr.local_vars loop.loop_test)
          |> Set.to_list
        in
        let+ curr_loop_arg_var_decls =
          Rewriter.List.map curr_loop_args ~f:(fun var ->
              let+ symbol =
                Rewriter.find_and_reify var.ident_loc (QualIdent.from_ident var)
              in

              match symbol with
              | VarDef v -> v.var_decl
              | _ ->
                  Error.error stmt.stmt_loc
                    ("Expected a variable (1); found " ^ Symbol.to_string symbol
                   ^ " for var: " ^ Ident.to_string var))
        in

        (* redefined loop_args for uniqueness *)
        let loop_arg_var_decls =
          List.map curr_loop_arg_var_decls ~f:(fun var_decl ->
              let new_var_name =
                Ident.fresh stmt.stmt_loc var_decl.var_name.ident_name
              in
              Logs.debug (fun m ->
                  m "Loop old_var_name: %a" Ident.pr var_decl.var_name);
              Logs.debug (fun m ->
                  m "Loop new_var_name: %a" Ident.pr new_var_name);
              let new_new_var_name =
                Ident.fresh stmt.stmt_loc var_decl.var_name.ident_name
              in
              Logs.debug (fun m ->
                  m "Loop new_new_var_name: %a" Ident.pr new_new_var_name);
              { var_decl with var_name = new_var_name }
              (* { var_decl with var_name = Ident.fresh stmt.stmt_loc var_decl.var_name.ident_name } *))
        in

        Logs.debug (fun m ->
            m "Loop curr_loop_arg_var_decls:\n %a"
              (Print.pr_list_comma Ident.pr)
              (List.map curr_loop_arg_var_decls ~f:(fun var_decl ->
                   var_decl.var_name)));

        Logs.debug (fun m ->
            m "Loop loop_arg_var_decls:\n %a"
              (Print.pr_list_comma Ident.pr)
              (List.map loop_arg_var_decls ~f:(fun var_decl ->
                   var_decl.var_name)));

        let loop_arg_renaming_map =
          List.fold2_exn curr_loop_arg_var_decls loop_arg_var_decls
            ~init:(Map.empty (module QualIdent))
            ~f:(fun map old_var_decl new_var_decl ->
              Map.add_exn map
                ~key:(QualIdent.from_ident old_var_decl.var_name)
                ~data:(Expr.from_var_decl new_var_decl))
        in

        let loop_arg_renaming_qual_ident_map =
          List.fold2_exn curr_loop_arg_var_decls loop_arg_var_decls
            ~init:(Map.empty (module QualIdent))
            ~f:(fun map old_var_decl new_var_decl ->
              Map.add_exn map
                ~key:(QualIdent.from_ident old_var_decl.var_name)
                ~data:(QualIdent.from_ident new_var_decl.var_name))
        in

        ( loop_arg_var_decls,
          loop_arg_renaming_map,
          loop_arg_renaming_qual_ident_map,
          curr_loop_arg_var_decls )
      in

      let* loop_ret_var_decls, loop_ret_renaming_map, curr_loop_ret_var_decls =
        (* Local variables modified from loop body become ret vals for loop procedure *)
        let curr_loop_rets = Stmt.stmt_local_vars_modified loop.loop_postbody in
        let+ curr_loop_ret_var_decls =
          Rewriter.List.map curr_loop_rets ~f:(fun var ->
              let+ symbol =
                Rewriter.find_and_reify stmt.stmt_loc (QualIdent.from_ident var)
              in

              match symbol with
              | VarDef v -> v.var_decl
              | _ ->
                  Error.error stmt.stmt_loc
                    ("Expected a variable (2); found " ^ Symbol.to_string symbol))
        in

        (* redefined loop_rets for uniqueness *)
        let loop_ret_var_decls =
          List.map curr_loop_ret_var_decls ~f:(fun var_decl ->
              {
                var_decl with
                var_name =
                  Ident.fresh stmt.stmt_loc var_decl.var_name.ident_name;
              })
        in

        let loop_ret_renaming_map =
          List.fold2_exn curr_loop_ret_var_decls loop_ret_var_decls
            ~init:(Map.empty (module QualIdent))
            ~f:(fun map old_var_decl new_var_decl ->
              Map.add_exn map
                ~key:(QualIdent.from_ident old_var_decl.var_name)
                ~data:(Expr.from_var_decl new_var_decl))
        in

        (loop_ret_var_decls, loop_ret_renaming_map, curr_loop_ret_var_decls)
      in

      let* loop_proc_name =
        let+ proc_name = Rewriter.current_scope_id in
        Ident.fresh stmt.stmt_loc (proc_name.qual_base.ident_name ^ "_loop")
      in

      (* Create new map which replaces loop_arg vars with loop_ret vars, for post conditions *)
      let loop_post_vars_renaming_map =
        Map.fold loop_ret_renaming_map ~init:loop_arg_renaming_map
          ~f:(fun ~key ~data map -> Map.set map ~key ~data)
      in

      let new_proc_decl =
        let loop_precond =
          List.map loop.loop_contract ~f:(fun spec ->
              {
                spec with
                spec_form =
                  Expr.alpha_renaming spec.spec_form loop_arg_renaming_map;
              })
        in

        let loop_postcond =
          List.map loop.loop_contract ~f:(fun spec ->
              {
                spec with
                spec_form =
                  Expr.alpha_renaming spec.spec_form loop_post_vars_renaming_map;
              })
        in

        (* Adding negation of loop_cond to postconditions *)
        let loop_postcond =
          loop_postcond
          @ [
              Stmt.mk_spec
                (Expr.mk_not ~loc:stmt.stmt_loc
                   (Expr.alpha_renaming loop.loop_test
                      loop_post_vars_renaming_map));
            ]
        in

        {
          Callable.call_decl_kind = Proc;
          call_decl_name = loop_proc_name;
          call_decl_formals = loop_arg_var_decls;
          call_decl_returns = loop_ret_var_decls;
          (* no locals, since all var_decls are removed earlier *)
          call_decl_locals = [];
          call_decl_precond = loop_precond;
          call_decl_postcond = loop_postcond;
          call_decl_is_free = false;
          call_decl_is_auto = false;
          call_decl_mask = None;
          call_decl_loc = stmt.stmt_loc;
        }
      in

      let* loop_body =
        let set_ret_vals_to_initial_args =
          List.map (Map.to_alist loop_ret_renaming_map)
            ~f:(fun (old_var, new_expr) ->
              Stmt.mk_assign ~loc [ new_expr ]
                (Map.find_exn loop_arg_renaming_map old_var))
        in

        let recurse_call =
          let lhs_list =
            List.map loop_ret_var_decls ~f:(fun var_decl ->
                QualIdent.from_ident var_decl.var_name)
          in

          let args_list =
            List.map loop_arg_var_decls ~f:(fun var_decl ->
                Expr.from_var_decl var_decl)
          in

          Stmt.mk_call ~loc ~lhs:lhs_list
            (QualIdent.from_ident loop_proc_name)
            args_list
        in

        (* TODO: Rename variables from curr_vars to loop_vars in loop body *)
        let* loop_body =
          Rewriter.Stmt.rewrite_qual_idents loop.loop_postbody
            ~f:(fun qual_ident ->
              Option.value
                (Map.find loop_arg_renaming_qual_ident_map qual_ident)
                ~default:qual_ident)
        in

        let cond_stmt =
          let test =
            Some (Expr.alpha_renaming loop.loop_test loop_arg_renaming_map)
          in
          let then_stmt = Stmt.mk_block_stmt ~loc [ loop_body; recurse_call ] in
          let else_stmt = Stmt.mk_skip ~loc in

          Stmt.mk_cond ~loc test then_stmt else_stmt
        in

        let ret_stmt =
          let ret_tuple =
            Expr.mk_tuple ~loc:stmt.stmt_loc
              (List.map loop_ret_var_decls ~f:(fun var_decl ->
                   Expr.from_var_decl var_decl))
          in

          Stmt.mk_return ~loc:stmt.stmt_loc ret_tuple
        in

        Rewriter.return
          (Stmt.mk_block_stmt ~loc:stmt.stmt_loc
             (set_ret_vals_to_initial_args @ [ cond_stmt; ret_stmt ]))
      in

      let loop_proc_symbol =
        let call_def =
          Callable.
            {
              call_decl = new_proc_decl;
              call_def = ProcDef { proc_body = Some loop_body };
            }
        in
        Module.CallDef call_def
      in

      Logs.debug (fun m ->
          m "Rewrites.rewrite_loops: Pre-typecheck loop_proc_symbol:\n %a"
            Symbol.pr loop_proc_symbol);

      let* _ =
        Rewriter.introduce_typecheck_symbol ~loc:stmt.stmt_loc
          ~f:Typing.process_symbol loop_proc_symbol
      in

      let* curr_state = Rewriter.__get_state in

      Logs.debug (fun m ->
          m "Rewrites.rewrite_loops: Loop introduced symbols:\n %a"
            (Print.pr_list_comma Symbol.pr)
            (List.hd_exn curr_state.state_new_symbols));

      Logs.debug (fun m ->
          m "Rewrites.rewrite_loops: Loop curr_scope:\n %a" QualIdent.pr
            curr_state.state_table.tbl_curr.scope_id);

      let new_stmt =
        let lhs_list =
          List.map curr_loop_ret_var_decls ~f:(fun var_decl ->
              QualIdent.from_ident var_decl.var_name)
        in
        let args_list =
          List.map curr_loop_arg_var_decls ~f:(fun var_decl ->
              Expr.from_var_decl var_decl)
        in

        Stmt.mk_call ~loc ~lhs:lhs_list
          (QualIdent.from_ident loop_proc_name)
          args_list
      in

      Logs.debug (fun m -> m "Loop new_stmt:\n %a" Stmt.pr new_stmt);
      Rewriter.return new_stmt
  | _ -> Rewriter.Stmt.descend stmt ~f:rewrite_loops

let rec rewrite_ret_stmts (stmt : Stmt.t) : Stmt.t Rewriter.t =
  let open Rewriter.Syntax in
  match stmt.stmt_desc with
  | Basic (Return ret_expr) ->
      let loc = Stmt.to_loc stmt in

      let* curr_proc_name = Rewriter.current_scope_id in

      let* callable_decl =
        Logs.debug (fun m ->
            m "Rewrites.rewrite_ret_stmts: curr_proc_name: %a" QualIdent.pr
              curr_proc_name);

        let+ symbol = Rewriter.find_and_reify stmt.stmt_loc curr_proc_name in

        match symbol with
        | CallDef c ->
            Logs.debug (fun m ->
                m "Rewrites.rewrite_ret_stmts: curr_proc: %a" Callable.pr c);
            c.call_decl
        | _ -> Error.error stmt.stmt_loc "Expected a call_def"
      in

      let ret_expr_list = Expr.unfold_tuple ret_expr in

      let renaming_map =
        List.fold2_exn callable_decl.call_decl_returns ret_expr_list
          ~init:(Map.empty (module QualIdent))
          ~f:(fun map var_decl expr ->
            Map.add_exn map
              ~key:(QualIdent.from_ident var_decl.var_name)
              ~data:expr)
      in

      let postconds_spec = callable_decl.call_decl_postcond in

      let postconds_exhale_stmts =
        if Callable.is_atomic callable_decl then
          let atomic_token_var =
            Expr.mk_var ~loc ~typ:Type.atomic_token
              (QualIdent.from_ident
                 (Rewriter.ProgUtils.callable_au_token_ident ~loc
                    callable_decl.call_decl_name))
          in

          let concrete_args =
            List.filter callable_decl.call_decl_formals ~f:(fun var_decl ->
                not var_decl.var_implicit)
          in
          let concrete_args_expr =
            List.map concrete_args ~f:Expr.from_var_decl
          in

          let error =
            ( Error.Verification,
              stmt.stmt_loc,
              "The atomic specification may not have been committed before \
               reaching this return point" )
          in

          let loc = Stmt.to_loc stmt in
          [
            Stmt.mk_exhale_expr ~cmnt:(Some "au_return_stmt") ~loc
              ~spec_error:[ Stmt.mk_const_spec_error error ]
              (Expr.mk_app ~loc ~typ:Type.perm
                 (Expr.AUPredCommit curr_proc_name)
                 ((atomic_token_var :: concrete_args_expr) @ [ ret_expr ]));
          ]
        else
          List.map postconds_spec ~f:(fun spec ->
              let expr = Expr.alpha_renaming spec.spec_form renaming_map in

              let error =
                ( Error.Verification,
                  stmt.stmt_loc,
                  "A postcondition may not hold at this return point" )
              in

              Stmt.mk_exhale_expr ~loc:stmt.stmt_loc
                ~cmnt:
                  (Some ("postconds added for ret_stmt: " ^ Stmt.to_string stmt))
                ~spec_error:(Stmt.mk_const_spec_error error :: spec.spec_error)
                expr)
      in

      let assume_false =
        Stmt.mk_assume_expr ~loc:stmt.stmt_loc
          (Expr.mk_bool ~loc:stmt.stmt_loc false)
      in

      let new_stmt =
        Stmt.mk_block_stmt ~loc:stmt.stmt_loc
          (postconds_exhale_stmts @ [ assume_false ])
      in

      Rewriter.return new_stmt
  | _ -> Rewriter.Stmt.descend stmt ~f:rewrite_ret_stmts

let rec rewrite_new_stmts (stmt : Stmt.t) : Stmt.t Rewriter.t =
  let open Rewriter.Syntax in
  match stmt.stmt_desc with
  | Basic (New new_desc) ->
      Logs.debug (fun m ->
          m "Rewrites.rewrite_new_stmts: new_desc: %a" Stmt.pr stmt);

      let* new_stmts =
        Rewriter.List.map new_desc.new_args ~f:(fun (field_name, expr_optn) ->
            let* field_val =
              match expr_optn with
              | Some expr -> Rewriter.return expr
              | None ->
                  Rewriter.ProgUtils.get_field_utils_id stmt.stmt_loc field_name
            in

            let* field_type =
              let* field_symbol =
                Rewriter.find_and_reify stmt.stmt_loc field_name
              in
              match field_symbol with
              | FieldDef f -> Rewriter.return f.field_type
              | _ -> Error.error stmt.stmt_loc "Expected a field_def"
            in

            let inhale_expr =
              Expr.mk_app ~typ:Type.perm ~loc:stmt.stmt_loc Expr.Own
                [
                  Expr.mk_var ~loc:stmt.stmt_loc ~typ:Type.ref new_desc.new_lhs;
                  Expr.mk_var ~loc:stmt.stmt_loc ~typ:field_type field_name;
                  field_val;
                ]
            in

            let inhale_stmt =
              Stmt.mk_inhale_expr
                ~cmnt:(Some ("new stmt: " ^ Stmt.to_string stmt))
                ~loc:stmt.stmt_loc inhale_expr
            in

            Rewriter.return inhale_stmt)
      in

      Rewriter.return (Stmt.mk_block_stmt ~loc:stmt.stmt_loc new_stmts)
  | _ -> Rewriter.Stmt.descend stmt ~f:rewrite_new_stmts

(** Replaces a `b := CAS(x.f, v1, v2)` stmt with `v := x.f; if (v == v1) { b := true; x.f := v2 } else { b := false }`. *)
let rec rewrite_cas_stmts (stmt : Stmt.t) : Stmt.t Rewriter.t =
  let open Rewriter.Syntax in
  match stmt.stmt_desc with
  | Basic (Cas cas_desc) ->
      let new_var_name =
        Ident.fresh stmt.stmt_loc (QualIdent.to_string cas_desc.cas_lhs ^ "$cas")
      in
      let new_var_decl =
        Type.mk_var_decl ~loc:stmt.stmt_loc ~ghost:true new_var_name
          (Expr.to_type cas_desc.cas_old_val)
      in
      let* _ =
        Rewriter.introduce_symbol
          (Module.VarDef { var_decl = new_var_decl; var_init = None })
      in
      let new_var_qualident = QualIdent.from_ident new_var_decl.var_name in
      let read_stmt =
        Stmt.mk_field_read ~loc:stmt.stmt_loc new_var_qualident
          cas_desc.cas_field cas_desc.cas_ref
      in
      let test_ =
        Some
          (Expr.mk_eq ~loc:stmt.stmt_loc
             (Expr.from_var_decl new_var_decl)
             cas_desc.cas_old_val)
      in
      let* symbol = Rewriter.find_and_reify stmt.stmt_loc cas_desc.cas_lhs in
      let lhs_var_decl =
        match symbol with
        | VarDef v -> v.var_decl
        | _ ->
            Error.error stmt.stmt_loc
              ("Expected a variable (3); found " ^ Symbol.to_string symbol)
      in
      let lhs_expr = Expr.from_var_decl lhs_var_decl in
      let then1_ =
        Stmt.mk_assign ~loc:stmt.stmt_loc [ lhs_expr ] (Expr.mk_bool true)
      in
      let* field_symbol =
        Rewriter.find_and_reify stmt.stmt_loc cas_desc.cas_field
      in
      let field_type, field_underlying_type =
        match field_symbol with
        | FieldDef f -> (
            match f.field_type with
            | App (Fld, [ tp_expr ], _) -> (f.field_type, tp_expr)
            | _ -> Error.type_error stmt.stmt_loc "Expected field identifier.")
        | _ -> Error.error stmt.stmt_loc "Expected a field_def"
      in
      let expr_attr = Expr.mk_attr stmt.stmt_loc field_underlying_type in
      let field_expr_attr = Expr.mk_attr stmt.stmt_loc field_type in
      let read_expr =
        Expr.App
          ( Read,
            [
              cas_desc.cas_ref;
              Expr.App (Var cas_desc.cas_field, [], field_expr_attr);
            ],
            expr_attr )
      in
      let then2_ =
        Stmt.mk_assign ~loc:stmt.stmt_loc [ read_expr ] cas_desc.cas_new_val
      in
      let then_ = Stmt.mk_block_stmt ~loc:stmt.stmt_loc [ then1_; then2_ ] in
      let else_ =
        Stmt.mk_assign ~loc:stmt.stmt_loc [ lhs_expr ] (Expr.mk_bool false)
      in
      let ite_stmt = Stmt.mk_cond ~loc:stmt.stmt_loc test_ then_ else_ in
      let new_stmts =
        Stmt.mk_block_stmt ~loc:stmt.stmt_loc [ read_stmt; ite_stmt ]
      in

      Rewriter.return new_stmts
  | _ -> Rewriter.Stmt.descend stmt ~f:rewrite_cas_stmts

(** Replaces a `fold p(x, y)` stmt with `exhale p(); inhale p.body`. *)
let rec rewrite_fold_unfold_stmts (stmt : Stmt.t) : Stmt.t Rewriter.t =
  let open Rewriter.Syntax in
  match stmt.stmt_desc with
  | Basic (Use use_desc) ->
      assert (match use_desc.use_kind with Fold | Unfold -> true | _ -> false);

      let* symbol = Rewriter.find_and_reify stmt.stmt_loc use_desc.use_name in

      let pred_decl, body =
        match symbol with
        | CallDef c ->
            let spec =
              match c.call_def with
              | ProcDef p ->
                  Error.error stmt.stmt_loc
                    "Expected a func_def inside a fold/unfold stmt"
              | FuncDef { func_body = None } ->
                  Error.error stmt.stmt_loc
                    "Empty func_def body inside a fold/unfold stmt not allowed"
              | FuncDef { func_body = Some e } -> e
            in

            (c.call_decl, Expr.set_loc spec (Stmt.to_loc stmt))
        | _ -> Error.error stmt.stmt_loc "Expected a call_def"
      in

      let renaming_map, fresh_dropped_args =
        (* let truncated_formal_args, dropped_formal_args = List.split_n pred_decl.call_decl_formals (List.length use_desc.use_args) in

           let fresh_dropped_args = List.map dropped_formal_args ~f:(fun var_decl ->
             { var_decl with var_name = Ident.fresh stmt.stmt_loc var_decl.var_name.ident_name; var_loc = stmt.stmt_loc; }
           ) in

           let fresh_dropped_args_exprs = List.map fresh_dropped_args ~f:(Expr.from_var_decl) in

           let renaming_map = List.fold2_exn (truncated_formal_args @ dropped_formal_args) (use_desc.use_args @ fresh_dropped_args_exprs) ~init:((Map.empty (module QualIdent))) ~f:(fun map var_decl arg_expr ->
             Map.add_exn map ~key:(QualIdent.from_ident var_decl.var_name) ~data:arg_expr
           )
           in *)
        let renaming_map =
          List.fold2_exn
            (pred_decl.call_decl_formals @ pred_decl.call_decl_returns)
            use_desc.use_args
            ~init:(Map.empty (module QualIdent))
            ~f:(fun map var_decl arg_expr ->
              Map.add_exn map
                ~key:(QualIdent.from_ident var_decl.var_name)
                ~data:arg_expr)
        in

        (* renaming_map, fresh_dropped_args *)
        (renaming_map, ())
      in

      let body_expr =
        let new_body = Expr.alpha_renaming body renaming_map in

        (* Expr.mk_binder ~loc:stmt.stmt_loc ~typ:Type.bool Exists fresh_dropped_args new_body  *)
        new_body
      in

      let pred_expr =
        Expr.mk_app ~loc:stmt.stmt_loc ~typ:Type.bool
          (Expr.Var use_desc.use_name) use_desc.use_args
      in

      let new_stmt =
        let inhale_stmt, exhale_stmt =
          match use_desc.use_kind with
          | Fold ->
              ( Stmt.mk_inhale_expr ~loc:stmt.stmt_loc
                  ~cmnt:(Some ("fold : " ^ Expr.to_string pred_expr))
                  pred_expr,
                let error =
                  ( Error.Verification,
                    stmt.stmt_loc,
                    "Failed to fold predicate. The body of the predicate may \
                     not hold at this point" )
                in
                Stmt.mk_exhale_expr ~loc:stmt.stmt_loc
                  ~cmnt:(Some ("fold : " ^ Expr.to_string pred_expr))
                  ~spec_error:[ Stmt.mk_const_spec_error error ]
                  body_expr )
          | Unfold ->
              ( Stmt.mk_inhale_expr ~loc:stmt.stmt_loc
                  ~cmnt:(Some ("unfold : " ^ Expr.to_string pred_expr))
                  body_expr,
                let error =
                  ( Error.Verification,
                    stmt.stmt_loc,
                    "Failed to unfold predicate. The predicate may not hold at \
                     this point" )
                in
                Stmt.mk_exhale_expr ~loc:stmt.stmt_loc
                  ~cmnt:(Some ("unfold : " ^ Expr.to_string pred_expr))
                  ~spec_error:[ Stmt.mk_const_spec_error error ]
                  pred_expr )
          | _ -> assert false
        in

        Stmt.mk_block_stmt ~loc:stmt.stmt_loc [ exhale_stmt; inhale_stmt ]
      in

      Rewriter.return new_stmt
  | _ -> Rewriter.Stmt.descend stmt ~f:rewrite_fold_unfold_stmts

let rec rewrite_call_stmts (stmt : Stmt.t) : Stmt.t Rewriter.t =
  let open Rewriter.Syntax in
  match stmt.stmt_desc with
  | Basic (Call call_desc) -> (
      let* symbol = Rewriter.find_and_reify stmt.stmt_loc call_desc.call_name in

      let call_decl, call_def =
        match symbol with
        | CallDef c -> (c.call_decl, c.call_def)
        | _ -> Error.error stmt.stmt_loc "Expected a call_def"
      in

      let* lhs_list =
        Rewriter.List.map call_desc.call_lhs ~f:(fun qual_iden ->
            let* symbol = Rewriter.find_and_reify stmt.stmt_loc qual_iden in

            match symbol with
            | VarDef v -> Rewriter.return v.var_decl
            | _ ->
                Error.error stmt.stmt_loc
                  ("Expected a variable (3); found " ^ Symbol.to_string symbol))
      in

      let* new_lhs_list =
        Rewriter.List.map lhs_list ~f:(fun lhs ->
            let new_var_name =
              Ident.fresh stmt.stmt_loc (lhs.var_name.ident_name ^ "$ret")
            in
            let new_var_decl = { lhs with var_name = new_var_name } in
            let* _ =
              Rewriter.introduce_symbol
                (Module.VarDef { var_decl = new_var_decl; var_init = None })
            in

            Rewriter.return (Expr.from_var_decl new_var_decl))
      in

      let* ( quant_renaming_map,
             quant_dropped_args,
             new_renaming_map,
             new_dropped_args ) =
        let truncated_formal_args, dropped_formal_args =
          List.split_n call_decl.call_decl_formals
            (List.length call_desc.call_args)
        in

        let fresh_dropped_args =
          List.map dropped_formal_args ~f:(fun var_decl ->
              {
                var_decl with
                var_name =
                  Ident.fresh stmt.stmt_loc var_decl.var_name.ident_name;
                var_loc = stmt.stmt_loc;
              })
        in

        let fresh_dropped_args_exprs =
          List.map fresh_dropped_args ~f:Expr.from_var_decl
        in

        (* Need to ensure that call_decl_returns and call_desc.call_lhs line up *)
        let renaming_map =
          List.fold2_exn
            (truncated_formal_args @ dropped_formal_args
           @ call_decl.call_decl_returns)
            (call_desc.call_args @ fresh_dropped_args_exprs @ new_lhs_list)
            ~init:(Map.empty (module QualIdent))
            ~f:(fun map var_decl arg_expr ->
              Map.add_exn map
                ~key:(QualIdent.from_ident var_decl.var_name)
                ~data:arg_expr)
        in

        let fresh_dropped_args2 =
          List.map dropped_formal_args ~f:(fun var_decl ->
              {
                var_decl with
                var_name =
                  Ident.fresh stmt.stmt_loc var_decl.var_name.ident_name;
                var_loc = stmt.stmt_loc;
              })
        in

        let fresh_dropped_args2_exprs =
          List.map fresh_dropped_args2 ~f:Expr.from_var_decl
        in

        (* Need to ensure that call_decl_returns and call_desc.call_lhs line up *)
        let renaming_map2 =
          List.fold2_exn
            (truncated_formal_args @ dropped_formal_args
           @ call_decl.call_decl_returns)
            (call_desc.call_args @ fresh_dropped_args2_exprs @ new_lhs_list)
            ~init:(Map.empty (module QualIdent))
            ~f:(fun map var_decl arg_expr ->
              Map.add_exn map
                ~key:(QualIdent.from_ident var_decl.var_name)
                ~data:arg_expr)
        in

        Rewriter.return
          (renaming_map, fresh_dropped_args, renaming_map2, fresh_dropped_args2)
      in

      Logs.debug (fun m ->
          m "Rewrites.rewrite_call_stmts: new_renaming_map: %a"
            (Util.Print.pr_map ~key:QualIdent.pr ~value:Expr.pr)
            new_renaming_map);

      match call_def with
      | ProcDef _ ->
          let* _ =
            Rewriter.List.map new_dropped_args ~f:(fun var ->
                Rewriter.introduce_symbol
                  (Module.VarDef { var_decl = var; var_init = None }))
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
          let error =
            ( Error.Verification,
              stmt.stmt_loc,
              "A precondition may not hold for this call" )
          in

          let assert_stmt =
            Stmt.mk_assert_expr ~loc:stmt.stmt_loc
              ~cmnt:(Some ("Assert stmt for Call: " ^ Stmt.to_string stmt))
              ~spec_error:[ Stmt.mk_const_spec_error error ]
                (* TODO: can we preserve the error messages for the individual preconditions here? *)
              (Expr.mk_binder ~loc:stmt.stmt_loc Exists quant_dropped_args
                 (Expr.mk_and
                    (List.map call_decl.call_decl_precond ~f:(fun spec ->
                         Expr.alpha_renaming spec.spec_form quant_renaming_map))))
          in

          let bind_stmt =
            Stmt.mk_bind ~loc:stmt.stmt_loc
              (List.map new_dropped_args ~f:Expr.from_var_decl)
              (Expr.mk_and
                 (List.map call_decl.call_decl_precond ~f:(fun spec ->
                      Expr.alpha_renaming spec.spec_form new_renaming_map)))
          in

          let exhale_stmts =
            List.map call_decl.call_decl_precond ~f:(fun spec ->
                Stmt.mk_exhale_expr ~loc:stmt.stmt_loc
                  ~cmnt:(Some ("Exhale stmt for Call: " ^ Stmt.to_string stmt))
                  ~spec_error:(Stmt.mk_const_spec_error error :: spec.spec_error)
                  (Expr.alpha_renaming spec.spec_form new_renaming_map))
          in

          let inhale_stmt =
            Stmt.mk_inhale_expr ~loc:stmt.stmt_loc
              ~cmnt:(Some ("Inhale stmt for Call: " ^ Stmt.to_string stmt))
              (Expr.mk_and
                 (List.map call_decl.call_decl_postcond ~f:(fun spec ->
                      Expr.alpha_renaming spec.spec_form new_renaming_map)))
          in

          let reassign_lhs_stmt =
            Stmt.mk_assign ~loc:stmt.stmt_loc
              (List.map lhs_list ~f:Expr.from_var_decl)
              (Expr.mk_tuple new_lhs_list)
          in

          (* TODO: Need to havoc ret vars before inhaling postconditions *)
          let new_stmt =
            Stmt.mk_block_stmt ~loc:stmt.stmt_loc
              (* (if (List.is_empty call_decl.call_decl_precond ) then *)
              (* [inhale_stmt] *)
              (* else *)
              (match (new_dropped_args, lhs_list) with
              | [], [] -> exhale_stmts @ [ inhale_stmt ]
              | [], _ -> exhale_stmts @ [ inhale_stmt; reassign_lhs_stmt ]
              | _, [] ->
                  (assert_stmt :: bind_stmt :: exhale_stmts) @ [ inhale_stmt ]
              | _, _ ->
                  (assert_stmt :: bind_stmt :: exhale_stmts)
                  @ [ inhale_stmt; reassign_lhs_stmt ])
          in

          Rewriter.return new_stmt
      | FuncDef _ ->
          let exhale_stmts =
            List.map call_decl.call_decl_precond ~f:(fun spec ->
                Stmt.mk_exhale_spec
                  ~cmnt:(Some ("Call: " ^ Stmt.to_string stmt))
                  ~loc:stmt.stmt_loc spec)
          in

          let ret_typ =
            Type.mk_prod stmt.stmt_loc
              (List.map call_decl.call_decl_returns ~f:(fun var_decl ->
                   var_decl.var_type))
          in

          let new_assign_stmt =
            Stmt.mk_assign ~loc:stmt.stmt_loc new_lhs_list
              (Expr.mk_app ~loc:stmt.stmt_loc ~typ:ret_typ
                 (Expr.Var call_desc.call_name) call_desc.call_args)
          in

          let reassign_lhs_stmt =
            Stmt.mk_assign ~loc:stmt.stmt_loc
              (List.map lhs_list ~f:Expr.from_var_decl)
              (Expr.mk_tuple new_lhs_list)
          in

          let new_stmt =
            Stmt.mk_block_stmt ~loc:stmt.stmt_loc
              (match lhs_list with
              | [] -> exhale_stmts @ [ new_assign_stmt ]
              | _ -> exhale_stmts @ [ new_assign_stmt; reassign_lhs_stmt ])
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
          let pre_conds =
            List.filter_map c.call_decl.call_decl_precond ~f:(fun spec ->
                if spec.spec_atomic then None
                else
                  Some
                    (Stmt.mk_inhale_spec
                       ~cmnt:
                         (Some ("precond: " ^ Expr.to_string spec.spec_form))
                       ~loc:(Expr.to_loc spec.spec_form)
                       spec))
          and post_conds =
            List.filter_map c.call_decl.call_decl_postcond ~f:(fun spec ->
                if spec.spec_atomic then None
                else
                  let error =
                    ( Error.Verification,
                      loc |> Loc.to_end,
                      "A postcondition may not hold at this return point" )
                  in
                  let spec =
                    {
                      spec with
                      spec_error =
                        Stmt.mk_const_spec_error error :: spec.spec_error;
                    }
                  in
                  Some
                    (Stmt.mk_exhale_spec
                       ~cmnt:
                         (Some ("postcond: " ^ Expr.to_string spec.spec_form))
                       ~loc:(Expr.to_loc spec.spec_form)
                       spec))
          in

          let* pre_conds, post_conds =
            if not (Callable.is_atomic c.call_decl) then
              Rewriter.return (pre_conds, post_conds)
            else
              let* callable_fully_qual_name = Rewriter.current_scope_id in

              let atomic_token_var =
                Expr.mk_var ~loc ~typ:Type.atomic_token
                  (QualIdent.from_ident
                     (Rewriter.ProgUtils.callable_au_token_ident ~loc
                        c.call_decl.call_decl_name))
              in

              let concrete_args =
                List.filter c.call_decl.call_decl_formals ~f:(fun var_decl ->
                    not var_decl.var_implicit)
              in
              let concrete_args_expr =
                List.map concrete_args ~f:Expr.from_var_decl
              in

              let inhale_au =
                Stmt.mk_inhale_expr ~cmnt:(Some "au_precond") ~loc
                  (Expr.mk_app ~loc ~typ:Type.perm
                     (Expr.AUPred callable_fully_qual_name)
                     (atomic_token_var :: concrete_args_expr))
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
                    "The atomic specification may not have been committed \
                     before reaching this return point" )
                in
                Stmt.mk_exhale_expr ~cmnt:(Some "au_postcond") ~loc
                  ~spec_error:[ Stmt.mk_const_spec_error error ]
                  (Expr.mk_app ~loc ~typ:Type.perm
                     (Expr.AUPredCommit callable_fully_qual_name)
                     ((atomic_token_var :: concrete_args_expr) @ [ ret_expr ]))
              in

              Rewriter.return (inhale_au :: pre_conds, exhale_au :: post_conds)
          in

          let new_body =
            Stmt.mk_block_stmt ~loc (pre_conds @ [ body ] @ post_conds)
          in
          let new_proc =
            Callable.
              {
                call_decl = c.call_decl;
                call_def = ProcDef { proc_body = Some new_body };
              }
          in
          Rewriter.return new_proc)
  | FuncDef func -> Rewriter.return c

let rewrite_atomic_callable_token (c : Callable.t) : Callable.t Rewriter.t =
  let open Rewriter.Syntax in
  match c.call_def with
  | ProcDef proc -> (
      match proc.proc_body with
      | None -> Rewriter.return c
      | Some body ->
          let loc = Stmt.to_loc body in
          if not (Callable.is_atomic c.call_decl) then Rewriter.return c
          else
            let atomic_token_var =
              {
                Type.var_name =
                  Rewriter.ProgUtils.callable_au_token_ident ~loc
                    c.call_decl.call_decl_name;
                var_loc = loc;
                var_type = Type.atomic_token;
                var_const = false;
                var_ghost = true;
                var_implicit = false;
              }
            in

            let* _ =
              Rewriter.introduce_symbol
                (Module.VarDef { var_decl = atomic_token_var; var_init = None })
            in

            (* let* callable_fully_qual_name = Rewriter.current_scope_id in

               let inhale_au =
                 let concrete_args = List.filter c.call_decl.call_decl_formals ~f:(fun var_decl -> not var_decl.var_implicit) in
                 let concrete_args_expr = List.map concrete_args ~f:(Expr.from_var_decl) in

                 Stmt.mk_inhale_expr ~loc:(Stmt.loc body) (Expr.mk_app ~loc:(Stmt.loc body) ~typ:Type.perm (Expr.AUPred callable_fully_qual_name) (Expr.from_var_decl atomic_token_var :: concrete_args_expr)) in

               let new_body = Stmt.mk_block_stmt ~loc:(Stmt.loc body) [inhale_au; body] in *)
            (* let new_proc = Callable.{ c with call_def = ProcDef { proc_body = Some new_body } } in *)
            Rewriter.return c)
  | FuncDef func -> Rewriter.return c

let rec rewrite_frac_field_types (symbol : Module.symbol) :
    Module.symbol Rewriter.t =
  let open Rewriter.Syntax in
  match symbol with
  | ModDef _ | ModInst _ | TypeDef _ | ConstrDef _ | DestrDef _ | VarDef _
  | CallDef _ ->
      Rewriter.return symbol
  | FieldDef f ->
      let* is_field_an_ra =
        match f.field_type with
        | App (Fld, [ App (Var qual_iden, args, _) ], _) ->
            assert (List.is_empty args);

            let module_name = QualIdent.pop qual_iden in

            let* does_module_implement_ra =
              let* module_symbol =
                Rewriter.find_and_reify f.field_loc module_name
              in
              Rewriter.ProgUtils.does_symbol_implement_ra module_symbol
            in

            Rewriter.return does_module_implement_ra
        | _ -> Rewriter.return false
      in

      Logs.debug (fun m ->
          m "Rewrites.rewrite_frac_field_types: is_field_an_ra: %s -> %b"
            (Type.to_string f.field_type)
            is_field_an_ra);
      if is_field_an_ra then Rewriter.return symbol
      else
        let* field_type =
          Typing.ProcessTypeExpr.expand_type_expr f.field_type
        in
        let field_underlying_tp =
          match field_type with
          | App (Fld, [ tp_expr ], _) -> tp_expr
          | _ -> Error.type_error f.field_loc "Expected field identifier."
        in

        let* tp_module =
          Rewriter.ProgUtils.intros_type_module ~loc:f.field_loc
            ~f:Typing.process_symbol field_underlying_tp
        in

        let instantiated_frac_module =
          Module.ModInst
            {
              mod_inst_name =
                Rewriter.ProgUtils.field_type_to_frac_mod_ident ~loc:f.field_loc
                  field_type;
              mod_inst_type = Predefs.lib_cancellative_ra_mod_qual_ident;
              mod_inst_def =
                Some (Predefs.lib_frac_mod_qual_ident, [ tp_module ]);
              mod_inst_is_interface = false;
              mod_inst_loc = f.field_loc;
            }
        in

        (* let* topscope_name = Rewriter.ProgUtils.find_highest_valid_scope_type_expr f.field_loc field_underlying_tp in

           let topscope_name = match topscope_name with
             | Some topscope_name -> topscope_name
             | None -> Error.type_error f.field_loc ("Could not find a valid scope to add field " ^ (Ident.to_string f.field_name) ^ " to.")

           in *)
        let* frac_mod_name =
          Rewriter.introduce_typecheck_symbol ~loc:f.field_loc
            ~f:Typing.process_symbol instantiated_frac_module
        in

        let frac_type =
          Type.mk_fld f.field_loc
            (Type.mk_var f.field_loc
               (QualIdent.append frac_mod_name (Ident.make f.field_loc "T" 0)))
        in

        Rewriter.return (Module.FieldDef { f with field_type = frac_type })

let rec rewrite_own_expr_4_arg (expr : Expr.t) : Expr.t Rewriter.t =
  (* Rewrites expressions of the form `own(x, f, v, p)` to `own (x, f, Frac[f.type].frac_chunk(v, p))

     Essentially, makes a uniform 3-arg representation of all own expressions, frac-type as well as RA type.
  *)
  let open Rewriter.Syntax in
  Logs.debug (fun m ->
      m "Rewrites.rewrite_own_expr_4_arg: run on expr: %a" Expr.pr expr);

  match expr with
  | App (Own, [ expr1; expr2; expr3; expr4 ], expr_attr) ->
      Logs.debug (fun m ->
          m "Rewrites.rewrite_own_expr_4_arg: found expr: %a" Expr.pr expr);

      (* let field_type = match Expr.to_type expr2 with
           | App (Fld, [tp_expr], _) -> tp_expr
           | _ -> Error.type_error (Expr.to_loc expr2) "Expected field identifier."
         in *)
      let field_type = Expr.to_type expr2 in
      let* field_type = Typing.ProcessTypeExpr.expand_type_expr field_type in

      let+ expr3 =
        let expr3_1 = expr3 in
        let expr3_2 = expr4 in

        Logs.debug (fun m ->
            m
              "Rewrites.rewrite_own_expr_4_arg: intros_type_module started: \
               tp_module: %a"
              Type.pr field_type);

        let* frac_mod_name =
          Rewriter.resolve (Expr.to_loc expr)
            (QualIdent.from_ident
               (Rewriter.ProgUtils.field_type_to_frac_mod_ident
                  ~loc:(Expr.to_loc expr) field_type))
        in

        let frac_type =
          Type.mk_var (Expr.to_loc expr)
            (QualIdent.append frac_mod_name
               (Ident.make (Expr.to_loc expr) "T" 0))
        in
        (* let frac_constr = Rewriter.find_and_reify (Expr.to_loc expr) (QualIdent.append frac_mod_name (Ident.make (Expr.to_loc expr) "frac_chunk" 0)) in *)
        let expr3 =
          Expr.mk_app ~loc:(Expr.to_loc expr) ~typ:frac_type
            (Expr.DataConstr
               (QualIdent.append frac_mod_name
                  (Ident.make (Expr.to_loc expr) "frac_chunk" 0)))
            [ expr3_1; expr3_2 ]
        in

        Rewriter.return expr3
      in

      Expr.App (Own, [ expr1; expr2; expr3 ], expr_attr)
  | _ -> Rewriter.Expr.descend expr ~f:rewrite_own_expr_4_arg

let rec rewrite_new_fpu_stmt_heap_arg (stmt : Stmt.t) : Stmt.t Rewriter.t =
  let open Rewriter.Syntax in
  (* Logs.debug (fun m -> m "Rewrites.rewrite_new_fpu_stmt_heap_arg: stmt: %a" Stmt.pr stmt); *)
  match stmt.stmt_desc with
  | Basic (New new_desc) ->
      let* new_args =
        Rewriter.List.map new_desc.new_args ~f:(fun (field_name, expr_optn) ->
            match expr_optn with
            | None -> Rewriter.return (field_name, expr_optn)
            | Some expr ->
                let* expr_typ =
                  Typing.ProcessTypeExpr.expand_type_expr (Expr.to_type expr)
                in

                let* field_elem_type =
                  let+ field_symbol =
                    Rewriter.find_and_reify (Expr.to_loc expr) field_name
                  in

                  match field_symbol with
                  | FieldDef f -> (
                      match f.field_type with
                      | App (Fld, [ tp_expr ], _) -> tp_expr
                      | _ ->
                          Error.type_error (Expr.to_loc expr)
                            "Expected field identifier.")
                  | _ -> Error.error stmt.stmt_loc "Expected a field_def"
                in

                let* field_elem_typ_expanded =
                  Typing.ProcessTypeExpr.expand_type_expr field_elem_type
                in

                if Type.(expr_typ = field_elem_typ_expanded) then
                  Rewriter.return (field_name, expr_optn)
                else
                  let frac_mod_name =
                    match field_elem_type with
                    | App (Var qual_iden, _, _) -> QualIdent.pop qual_iden
                    | _ ->
                        Error.type_error (Expr.to_loc expr)
                          "Expected field identifier."
                  in

                  let frac_type =
                    Type.mk_var (Expr.to_loc expr)
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

      Rewriter.return
        { stmt with stmt_desc = Basic (New { new_desc with new_args }) }
  | Basic (Fpu fpu_desc) ->
      let compute_new_expr old_expr field_name =
        let loc = Expr.to_loc old_expr in
        let* expr_typ =
          Typing.ProcessTypeExpr.expand_type_expr (Expr.to_type old_expr)
        in

        let* field_elem_type =
          let+ field_symbol = Rewriter.find_and_reify loc field_name in

          match field_symbol with
          | FieldDef f -> (
              match f.field_type with
              | App (Fld, [ tp_expr ], _) -> tp_expr
              | _ -> Error.type_error loc "Expected field identifier.")
          | _ -> Error.error stmt.stmt_loc "Expected a field_def"
        in

        let* field_elem_typ_expanded =
          Typing.ProcessTypeExpr.expand_type_expr field_elem_type
        in

        if Type.(expr_typ = field_elem_typ_expanded) then
          Rewriter.return old_expr
        else
          let* field_type =
            let+ field_symbol = Rewriter.find_and_reify loc field_name in

            match field_symbol with
            | FieldDef f -> f.field_type
            | _ -> Error.error stmt.stmt_loc "Expected a field_def"
          in

          let frac_mod_name =
            match field_elem_type with
            | App (Var qual_iden, _, _) -> QualIdent.pop qual_iden
            | _ -> Error.type_error loc "Expected field identifier."
          in

          let frac_type =
            Type.mk_var loc
              (QualIdent.append frac_mod_name (Ident.make loc "T" 0))
          in
          let new_expr =
            Expr.mk_app ~loc ~typ:frac_type
              (Expr.DataConstr
                 (QualIdent.append frac_mod_name
                    (Ident.make loc "frac_chunk" 0)))
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

      let* fpu_new_val =
        compute_new_expr fpu_desc.fpu_new_val fpu_desc.fpu_field
      in

      let new_fpu_desc = { fpu_desc with fpu_old_val; fpu_new_val } in

      Rewriter.return { stmt with stmt_desc = Basic (Fpu new_fpu_desc) }
  | _ -> Rewriter.Stmt.descend stmt ~f:rewrite_new_fpu_stmt_heap_arg

let rewrite_add_predicate_validity_lemmas (c : Callable.t) :
    Callable.t Rewriter.t =
  let open Rewriter.Syntax in
  match c.call_decl.call_decl_kind with
  | Pred | Invariant -> (
      match (c.call_decl.call_decl_returns, c.call_def) with
      | [], _ | _, FuncDef { func_body = None } -> Rewriter.return c
      | rets, FuncDef { func_body = Some body } ->
          let pred_valid_lemma_ident =
            Ident.fresh c.call_decl.call_decl_loc
              ("pred_valid$" ^ Ident.to_string c.call_decl.call_decl_name)
          in

          let formal_args, renaming_map1, renaming_map2, preconds =
            let renamings, in_args =
              List.fold_map c.call_decl.call_decl_formals
                ~init:(Map.empty (module QualIdent))
                ~f:(fun acc_renamings var_decl ->
                  let new_var_decl =
                    {
                      var_decl with
                      var_name =
                        Ident.fresh var_decl.var_loc
                          var_decl.var_name.ident_name;
                    }
                  in
                  let new_var_expr = Expr.from_var_decl new_var_decl in

                  ( Map.add_exn acc_renamings
                      ~key:(QualIdent.from_ident var_decl.var_name)
                      ~data:new_var_expr,
                    new_var_decl ))
            in

            let renamings1, out_args1 =
              List.fold_map rets ~init:renamings
                ~f:(fun acc_renamings var_decl ->
                  let new_var_decl =
                    {
                      var_decl with
                      var_name =
                        Ident.fresh var_decl.var_loc
                          var_decl.var_name.ident_name;
                    }
                  in
                  let new_var_expr = Expr.from_var_decl new_var_decl in

                  ( Map.add_exn acc_renamings
                      ~key:(QualIdent.from_ident var_decl.var_name)
                      ~data:new_var_expr,
                    new_var_decl ))
            in

            let renamings2, out_args2 =
              List.fold_map rets ~init:renamings
                ~f:(fun acc_renamings var_decl ->
                  let new_var_decl =
                    {
                      var_decl with
                      var_name =
                        Ident.fresh var_decl.var_loc
                          var_decl.var_name.ident_name;
                    }
                  in
                  let new_var_expr = Expr.from_var_decl new_var_decl in

                  ( Map.add_exn acc_renamings
                      ~key:(QualIdent.from_ident var_decl.var_name)
                      ~data:new_var_expr,
                    new_var_decl ))
            in

            let preconds =
              List.map2_exn out_args1 out_args2 ~f:(fun out_arg1 out_arg2 ->
                  let spec_expr =
                    Expr.mk_not
                      (Expr.mk_eq ~loc:(Expr.to_loc body)
                         (Expr.from_var_decl out_arg1)
                         (Expr.from_var_decl out_arg2))
                  in

                  Stmt.mk_spec spec_expr)
            in

            (in_args @ out_args1 @ out_args2, renamings1, renamings2, preconds)
          in

          let postcond =
            Stmt.mk_spec (Expr.mk_bool ~loc:(Expr.to_loc body) false)
          in

          let call_decl =
            {
              Callable.call_decl_kind = Lemma;
              call_decl_name = pred_valid_lemma_ident;
              call_decl_formals = formal_args;
              call_decl_returns = [];
              call_decl_locals = [];
              call_decl_precond = preconds;
              call_decl_postcond = [ postcond ];
              call_decl_is_free = false;
              call_decl_is_auto = false;
              call_decl_mask = None;
              call_decl_loc = c.call_decl.call_decl_loc;
            }
          in

          let call_body =
            Stmt.mk_block_stmt ~loc:c.call_decl.call_decl_loc
              [
                Stmt.mk_inhale_expr ~loc:c.call_decl.call_decl_loc
                  (Expr.alpha_renaming body renaming_map1);
                Stmt.mk_inhale_expr ~loc:c.call_decl.call_decl_loc
                  (Expr.alpha_renaming body renaming_map2);
              ]
          in

          let call_def =
            Module.CallDef
              Callable.
                { call_decl; call_def = ProcDef { proc_body = Some call_body } }
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

module AtomicityAnalysis = struct
  type au_token = {
    token : QualIdent.t;
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
    if List.is_empty state.au_opened && List.is_empty state.invs_opened then
      state
    else
      match state.atomic_step_taken with
      | false -> { state with atomic_step_taken = true }
      | true ->
          Error.verification_error loc
            "Attempting to take more than one atomic step with an open \
             invariant or atomic update"

  let take_non_atomic_step ~loc (state : atomicity_check) : atomicity_check =
    if List.is_empty state.au_opened && List.is_empty state.invs_opened then
      state
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
           !"Cannot open invariant %{Ident}. Invariant already opened or not \
             in mask"
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
        "Invariant not already opened; cannot be closed. Invariant not in \
         mask; cannot be allocated."
    else
      let invs_opened =
        List.filter atomicity_state.invs_opened ~f:(fun inv ->
            not
              (QualIdent.(inv.inv_name = inv_name)
              && List.for_all2_exn inv_args inv.inv_args ~f:Expr.alpha_equal))
      in

      let mask = Set.add atomicity_state.mask inv_name in

      if List.is_empty invs_opened && List.is_empty atomicity_state.au_opened
      then { atomicity_state with invs_opened; mask; atomic_step_taken = false }
      else { atomicity_state with invs_opened; mask }

  let open_au ~loc (token, callable, callable_args, implicit_bound_vars)
      atomicity_state : atomicity_check =
    if
      List.exists atomicity_state.au_opened ~f:(fun au ->
          QualIdent.(au.token = token))
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
             QualIdent.(au.token = token)))
    then Error.error loc "Atomic token not already opened"
    else
      let au_opened =
        List.filter atomicity_state.au_opened ~f:(fun au ->
            not QualIdent.(au.token = token))
      in

      if List.is_empty au_opened && List.is_empty atomicity_state.invs_opened
      then { atomicity_state with au_opened; atomic_step_taken = false }
      else { atomicity_state with au_opened }

  let rec is_expr_atomic (expr : Expr.t) : bool =
    match expr with
    | App (constr, expr_args, _) -> (
        match constr with
        | Null | Int _ | Real _ | Bool _ -> true
        | Var _ -> ( match expr_args with [] -> true | _ -> false)
        | Read | Cas -> is_expr_atomic (List.hd_exn expr_args)
        | _ -> false)
    | _ -> false

  let rewrite_au_cmnds ~(ghost_block : bool) (stmt : Stmt.t) :
      (Stmt.t, atomicity_check) Rewriter.t_ext =
    let open Rewriter.Syntax in
    let rec rewrite_au_cmnds ~(ghost_block : bool) (stmt : Stmt.t) :
        (Stmt.t, atomicity_check) Rewriter.t_ext =
      let* curr_callable_name = Rewriter.current_scope_id in
      let* curr_callable =
        let* symbol =
          Rewriter.find_and_reify stmt.stmt_loc curr_callable_name
        in
        match symbol with
        | CallDef c -> Rewriter.return c
        | _ -> Error.error stmt.stmt_loc "Expected a call_def"
      in

      let concrete_args =
        List.filter curr_callable.call_decl.call_decl_formals
          ~f:(fun var_decl -> not var_decl.var_implicit)
      in
      let implicit_args =
        List.filter curr_callable.call_decl.call_decl_formals
          ~f:(fun var_decl -> var_decl.var_implicit)
      in

      Logs.debug (fun m ->
          m "Rewrites.rewrite_au_cmnds: curr_callable_name: %a" QualIdent.pr
            curr_callable_name);

      let loc = stmt.stmt_loc in

      let* atomicity_state = Rewriter.current_user_state in

      match stmt.stmt_desc with
      | Basic (New new_desc) ->
          let* new_lhs =
            let* symbol =
              Rewriter.find_and_reify stmt.stmt_loc new_desc.new_lhs
            in
            match symbol with
            | VarDef v -> Rewriter.return v
            | _ -> Error.error stmt.stmt_loc "Expected a var_def"
          in

          if new_lhs.var_decl.var_ghost then Rewriter.return stmt
          else if ghost_block then
            Error.error stmt.stmt_loc
              "Cannot allocate non-ghost variables in a ghost block"
          else
            let atomicity_state = take_atomic_step ~loc atomicity_state in
            let* _ = Rewriter.set_user_state atomicity_state in
            Rewriter.return stmt
      | Basic (Assign assign_desc) ->
          let* is_assign_desc_lhs_ghost =
            Rewriter.List.for_all assign_desc.assign_lhs ~f:(fun expr ->
                match expr with
                | App (Var qual_iden, [], _) -> (
                    let* symbol =
                      Rewriter.find_and_reify stmt.stmt_loc qual_iden
                    in
                    match symbol with
                    | VarDef v -> Rewriter.return v.var_decl.var_ghost
                    | _ -> Error.error stmt.stmt_loc "Expected a var_def")
                | App (Read, [ loc_expr; field_expr ], _) ->
                    Rewriter.return false
                | _ -> Error.error stmt.stmt_loc "Expected a variable")
          in

          if is_assign_desc_lhs_ghost then Rewriter.return stmt
          else if ghost_block then
            Error.error stmt.stmt_loc
              "Cannot assign to non-ghost variables in a ghost block"
          else if List.length assign_desc.assign_lhs > 1 then
            let atomicity_state = take_non_atomic_step ~loc atomicity_state in
            let* _ = Rewriter.set_user_state atomicity_state in
            Rewriter.return stmt
          else if is_expr_atomic assign_desc.assign_rhs then
            let atomicity_state = take_atomic_step ~loc atomicity_state in
            let* _ = Rewriter.set_user_state atomicity_state in
            Rewriter.return stmt
          else
            let atomicity_state = take_non_atomic_step ~loc atomicity_state in
            let* _ = Rewriter.set_user_state atomicity_state in
            Rewriter.return stmt
      | Basic (Bind bind_desc) ->
          let* is_bind_lhs_ghost =
            Rewriter.List.for_all bind_desc.bind_lhs ~f:(fun expr ->
                match expr with
                | App (Var qual_iden, [], _) -> (
                    let* symbol =
                      Rewriter.find_and_reify stmt.stmt_loc qual_iden
                    in
                    match symbol with
                    | VarDef v -> Rewriter.return v.var_decl.var_ghost
                    | _ -> Error.error stmt.stmt_loc "Expected a var_def")
                | _ -> Error.error stmt.stmt_loc "Expected a variable")
          in

          if is_bind_lhs_ghost then Rewriter.return stmt
          else Error.error stmt.stmt_loc "Cannot bind non-ghost variables"
      | Basic (FieldRead field_read_desc) -> (
          let* symbol =
            Rewriter.find_and_reify stmt.stmt_loc field_read_desc.field_read_lhs
          in
          match symbol with
          | VarDef v ->
              if v.var_decl.var_ghost then Rewriter.return stmt
              else
                let atomicity_state = take_atomic_step ~loc atomicity_state in
                let* _ = Rewriter.set_user_state atomicity_state in
                Rewriter.return stmt
          | _ -> Error.error stmt.stmt_loc "Expected a var_def")
      | Basic (Cas cas_desc) ->
          let atomicity_state = take_atomic_step ~loc atomicity_state in
          let* _ = Rewriter.set_user_state atomicity_state in
          Rewriter.return stmt
      | Basic (Havoc qual_iden) -> (
          let* symbol = Rewriter.find_and_reify stmt.stmt_loc qual_iden in
          match symbol with
          | VarDef v ->
              if v.var_decl.var_ghost then Rewriter.return stmt
              else if ghost_block then
                Error.error stmt.stmt_loc
                  "Cannot havoc non-ghost variables in a ghost block"
              else
                let atomicity_state = take_atomic_step ~loc atomicity_state in
                let* _ = Rewriter.set_user_state atomicity_state in
                Rewriter.return stmt
          | _ -> Error.error stmt.stmt_loc "Expected a var_def")
      | Basic (Call call_desc) ->
          let* symbol =
            Rewriter.find_and_reify stmt.stmt_loc call_desc.call_name
          in
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
                  let* symbol =
                    Rewriter.find_and_reify stmt.stmt_loc qual_iden
                  in
                  match symbol with
                  | VarDef v -> Rewriter.return v.var_decl.var_ghost
                  | _ -> Error.error stmt.stmt_loc "Expected a var_def")
            in

            if
              (is_call_lhs_ghost && not (List.is_empty call_desc.call_lhs))
              || Poly.(call_decl.call_decl_kind = Lemma)
            then Rewriter.return stmt
            else if ghost_block then
              Error.error stmt.stmt_loc
                "Cannot assign to non-ghost variables in a ghost block"
            else if Callable.is_atomic call_decl then
              let atomicity_state = take_atomic_step ~loc atomicity_state in
              let* _ = Rewriter.set_user_state atomicity_state in
              Rewriter.return stmt
            else
              let atomicity_state = take_non_atomic_step ~loc atomicity_state in
              let* _ = Rewriter.set_user_state atomicity_state in
              Rewriter.return stmt
      | Basic (Return return_expr) ->
          if ghost_block then
            Error.error stmt.stmt_loc "Cannot return in a ghost block"
          else if is_expr_atomic return_expr then
            let atomicity_state = take_atomic_step ~loc atomicity_state in
            let* _ = Rewriter.set_user_state atomicity_state in
            Rewriter.return stmt
          else
            let atomicity_state = take_non_atomic_step ~loc atomicity_state in
            let* _ = Rewriter.set_user_state atomicity_state in
            Rewriter.return stmt
      | Basic (Use use_desc) -> (
          let* symbol =
            Rewriter.find_and_reify stmt.stmt_loc use_desc.use_name
          in
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
                    | OpenInv | CloseInv ->
                        Error.internal_error stmt.stmt_loc "Unsupported"
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
                let+ symbol = Rewriter.find_and_reify stmt.stmt_loc qual_iden in
                match symbol with
                | VarDef v -> v
                | _ -> Error.error stmt.stmt_loc "Expected a var_def"
              in

              let* au_token_var =
                let+ symbol =
                  Rewriter.find_and_reify stmt.stmt_loc
                    (QualIdent.from_ident
                       (Rewriter.ProgUtils.callable_au_token_ident ~loc
                          (QualIdent.unqualify curr_callable_name)))
                in
                match symbol with
                | VarDef v -> v
                | _ -> Error.error stmt.stmt_loc "Expected a var_def"
              in

              let assign_stmt =
                Stmt.mk_assign ~loc
                  [ Expr.from_var_decl qual_iden_var.var_decl ]
                  (Expr.from_var_decl au_token_var.var_decl)
              in

              Rewriter.return assign_stmt
          | OpenAU (token, callable, bound_vars) -> (
              let exhale_stmt =
                Stmt.mk_exhale_expr
                  ~cmnt:(Some ("OpenAU: " ^ Stmt.to_string stmt))
                  ~loc
                  (Expr.mk_app ~loc ~typ:Type.perm (AUPred curr_callable_name)
                     (Expr.mk_var ~typ:Type.atomic_token token
                     :: List.map concrete_args ~f:Expr.from_var_decl))
              in

              match callable with
              | Some _ ->
                  Error.error stmt.stmt_loc
                    "Unsupported to open another callable"
              | None ->
                  let alpha_renaming_map =
                    List.fold2_exn implicit_args bound_vars
                      ~init:(Map.empty (module QualIdent))
                      ~f:(fun acc_map implicit_arg bound_var ->
                        Map.add_exn acc_map
                          ~key:(QualIdent.from_ident implicit_arg.var_name)
                          ~data:bound_var)
                  in

                  let inhale_stmts =
                    List.filter_map curr_callable.call_decl.call_decl_precond
                      ~f:(fun spec ->
                        if not spec.spec_atomic then None
                        else
                          Some
                            (Stmt.mk_inhale_expr
                               ~cmnt:(Some ("OpenAU: " ^ Stmt.to_string stmt))
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
                    QualIdent.equal au_token.token token)
              in

              let opened_au_token =
                match opened_au_token with
                | None ->
                    Error.error stmt.stmt_loc
                      "No opened AU token found to abort"
                | Some opened_au_token -> opened_au_token
              in

              let* callable_decl =
                let+ symbol =
                  Rewriter.find_and_reify stmt.stmt_loc opened_au_token.callable
                in
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
                                "An atomic precondition may no longer hold \
                                 when aborting the atomic update." )
                            in
                            Some
                              (Stmt.mk_exhale_expr
                                 ~cmnt:
                                   (Some ("AbortAU: " ^ Stmt.to_string stmt))
                                 ~loc
                                 ~spec_error:
                                   (Stmt.mk_const_spec_error error
                                   :: spec.spec_error)
                                 (Expr.alpha_renaming spec.spec_form
                                    alpha_renaming_map)))
                    in

                    let inhale_stmt =
                      Stmt.mk_inhale_expr
                        ~cmnt:(Some ("AbortAU: " ^ Stmt.to_string stmt))
                        ~loc
                        (Expr.mk_app ~loc ~typ:Type.perm
                           (AUPred opened_au_token.callable)
                           (Expr.mk_var ~typ:Type.atomic_token
                              opened_au_token.token
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
                                 ~cmnt:
                                   (Some ("CommitAU: " ^ Stmt.to_string stmt))
                                 ~loc
                                 ~spec_error:
                                   (Stmt.mk_const_spec_error error
                                   :: spec.spec_error)
                                 (Expr.alpha_renaming spec.spec_form
                                    alpha_renaming_map)))
                    in

                    let inhale_stmt =
                      Stmt.mk_inhale_expr
                        ~cmnt:(Some ("CommitAU: " ^ Stmt.to_string stmt))
                        ~loc
                        (Expr.mk_app ~loc ~typ:Type.perm
                           (AUPredCommit opened_au_token.callable)
                           (Expr.mk_var ~typ:Type.atomic_token
                              opened_au_token.token
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
      | Block block_desc when block_desc.block_is_ghost ->
          Rewriter.Stmt.descend stmt ~f:(rewrite_au_cmnds ~ghost_block:true)
      | Block block_desc ->
          Rewriter.Stmt.descend stmt ~f:(rewrite_au_cmnds ~ghost_block)
      | Cond cond_desc ->
          let* then_stmt =
            Rewriter.Stmt.descend cond_desc.cond_then
              ~f:(rewrite_au_cmnds ~ghost_block)
          in
          let* then_atomicity_state = Rewriter.current_user_state in

          let* _ = Rewriter.set_user_state atomicity_state in
          let* else_stmt =
            Rewriter.Stmt.descend cond_desc.cond_else
              ~f:(rewrite_au_cmnds ~ghost_block)
          in
          let* else_atomicity_state = Rewriter.current_user_state in

          let if_else_atomicity_states_equal =
            if
              List.length then_atomicity_state.invs_opened
              = List.length else_atomicity_state.invs_opened
              && List.length then_atomicity_state.au_opened
                 = List.length else_atomicity_state.au_opened
            then
              List.for_all2_exn then_atomicity_state.invs_opened
                else_atomicity_state.invs_opened ~f:(fun inv1 inv2 ->
                  QualIdent.equal inv1.inv_name inv2.inv_name
                  && List.for_all2_exn inv1.inv_args inv2.inv_args
                       ~f:Expr.alpha_equal)
              && List.for_all2_exn then_atomicity_state.au_opened
                   else_atomicity_state.au_opened ~f:(fun au1 au2 ->
                     QualIdent.equal au1.token au2.token
                     && QualIdent.equal au1.callable au2.callable
                     && List.for_all2_exn au1.callable_args au2.callable_args
                          ~f:Expr.alpha_equal
                     && List.for_all2_exn au1.implicit_bound_vars
                          au2.implicit_bound_vars ~f:Expr.alpha_equal)
              (* && Bool.(then_atomicity_state.atomic_step_taken = else_atomicity_state.atomic_step_taken) *)
            else false
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

            if ghost_block then Rewriter.return new_stmt
            else
              let atomicity_state =
                take_non_atomic_step ~loc else_atomicity_state
              in
              let* _ = Rewriter.set_user_state atomicity_state in
              Rewriter.return new_stmt
          else
            Error.error stmt.stmt_loc
              "Inconsistent atomicity states in then and else branches"
      | _ -> Rewriter.Stmt.descend stmt ~f:(rewrite_au_cmnds ~ghost_block)
    in

    let* stmt = rewrite_au_cmnds ~ghost_block stmt in
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
          "Rewrites.rewrite_atomicity_analysis: Rewriting atomicity analysis \
           for callable: %a"
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
        (Rewriter.Callable.rewrite_stmts
           ~f:(rewrite_au_cmnds ~ghost_block:false)
           c)
    in

    c
end

let rewrite_introduce_heaps (c : Callable.t) : Callable.t Rewriter.t =
  let open Rewriter.Syntax in
  Logs.debug (fun m ->
      m "Rewrites.rewrite_introduce_heaps: Introducing heaps in callable: %a"
        Ident.pr c.call_decl.call_decl_name);
  match c.call_def with
  | FuncDef _ -> Rewriter.return c
  | ProcDef { proc_body = None } -> Rewriter.return c
  | ProcDef { proc_body = Some body } ->
      let* preds_list = Rewriter.ProgUtils.stmt_preds_mentioned body in
      let fields_list = Stmt.stmt_fields_accessed body in
      let au_preds_list = Set.to_list (Stmt.stmt_au_preds_referenced body) in

      Logs.debug (fun m ->
          m "Rewrites.rewrite_introduce_heaps: Predicates mentioned in the body");

      let* body =
        HeapsExplicitTrnsl.introduce_heaps_in_stmts
          ~loc:c.call_decl.call_decl_loc ~fields_list ~preds_list ~au_preds_list
          body
      in

      Rewriter.return { c with call_def = ProcDef { proc_body = Some body } }

let rec rewrite_ssa_stmts (s : Stmt.t) :
    (Stmt.t, var_decl ident_map) Rewriter.t_ext =
  let open Rewriter.Syntax in
  let* var_map = Rewriter.current_user_state in
  let subst_map =
    Map.map var_map ~f:(fun var_decl -> Expr.from_var_decl var_decl)
  in
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
            Stmt.
              {
                s with
                stmt_desc = Basic (Spec (spec_kind, { spec with spec_form }));
              }
      | Assign assign_stmt ->
          let assign_rhs =
            Expr.alpha_renaming assign_stmt.assign_rhs subst_map
          in
          let* assign_lhs =
            Rewriter.List.map assign_stmt.assign_lhs ~f:(fun lhs_expr ->
                let* var_map = Rewriter.current_user_state in

                if Expr.is_ident lhs_expr then (
                  let local_var = Expr.to_ident lhs_expr in

                  Logs.debug (fun m ->
                      m
                        "Rewrites.rewrite_ssa_stmts: Assigning to local \
                         variable %a; for stmt %a"
                        Ident.pr local_var Stmt.pr s);
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
                      (VarDef { var_decl = new_var_decl; var_init = None })
                  in

                  let var_map =
                    Map.set var_map ~key:local_var ~data:new_var_decl
                  in

                  let+ _ = Rewriter.set_user_state var_map in

                  Expr.from_var_decl new_var_decl)
                else Rewriter.return lhs_expr)
          in

          Rewriter.return
            Stmt.
              {
                s with
                stmt_desc =
                  Basic (Assign { assign_stmt with assign_lhs; assign_rhs });
              }
      | Havoc qual_iden ->
          if QualIdent.is_local qual_iden then (
            let local_var = QualIdent.to_ident qual_iden in

            Logs.debug (fun m ->
                m "Rewrites.rewrite_ssa_stmts: Havocing local variable %a"
                  Ident.pr local_var);
            let old_var_decl = Map.find_exn var_map local_var in
            let new_var_decl =
              {
                old_var_decl with
                var_name =
                  Ident.fresh old_var_decl.var_loc
                    old_var_decl.var_name.ident_name;
              }
            in

            let* _ =
              Rewriter.introduce_symbol
                (VarDef { var_decl = new_var_decl; var_init = None })
            in

            let var_map = Map.set var_map ~key:local_var ~data:new_var_decl in

            let+ _ = Rewriter.set_user_state var_map in

            Stmt.mk_block_stmt ~loc:s.stmt_loc [])
          else Rewriter.return s
      | Bind bind_stmt ->
          let* bind_lhs =
            Rewriter.List.map bind_stmt.bind_lhs ~f:(fun lhs_expr ->
                let* var_map = Rewriter.current_user_state in

                if Expr.is_ident lhs_expr then
                  let local_var = Expr.to_ident lhs_expr in

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
                      (VarDef { var_decl = new_var_decl; var_init = None })
                  in

                  let var_map =
                    Map.set var_map ~key:local_var ~data:new_var_decl
                  in

                  let+ _ = Rewriter.set_user_state var_map in

                  Expr.from_var_decl new_var_decl
                else Rewriter.return lhs_expr)
          in

          let* var_map = Rewriter.current_user_state in
          let subst_map =
            Map.map var_map ~f:(fun var_decl -> Expr.from_var_decl var_decl)
          in
          let subst_map =
            (Map.map_keys_exn (module QualIdent)) subst_map ~f:(fun ident ->
                QualIdent.from_ident ident)
          in

          let bind_rhs = Expr.alpha_renaming bind_stmt.bind_rhs subst_map in

          Rewriter.return
            Stmt.{ s with stmt_desc = Basic (Bind { bind_lhs; bind_rhs }) }
      | _ ->
          Logs.debug (fun m ->
              m "Rewrites.rewrite_ssa_stmts: Skipping statement %a" Stmt.pr s);
          assert false)
  | Block block_stmt ->
      let+ block_body =
        Rewriter.List.map block_stmt.block_body ~f:rewrite_ssa_stmts
      in

      Stmt.mk_block_stmt ~ghost:block_stmt.block_is_ghost ~loc:s.stmt_loc
        block_body
      (* { s with stmt_desc = Block { block_stmt with block_body; } } *)
  | Cond cond_stmt when not cond_stmt.cond_if_assumes_false ->
      let cond_test =
        Option.map
          ~f:(fun test -> Expr.alpha_renaming test subst_map)
          cond_stmt.cond_test
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
                if
                  Ident.(
                    Type.(then_var_decl.var_name)
                    = Type.(else_var_decl.var_name))
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
                  Ident.fresh old_var_decl.var_loc
                    old_var_decl.var_name.ident_name;
              }
            in

            let+ _ =
              Rewriter.introduce_symbol
                (VarDef { var_decl = new_var_decl; var_init = None })
            in

            Map.set map ~key:var ~data:new_var_decl)
      in

      let cond_then_assigns =
        List.map updated_vals ~f:(fun var ->
            let old_var_decl = Map.find_exn cond_then_map var in
            let new_var_decl = Map.find_exn new_var_map var in

            Stmt.mk_assign ~loc:s.stmt_loc
              [ Expr.from_var_decl new_var_decl ]
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
              [ Expr.from_var_decl new_var_decl ]
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
            Cond
              { cond_test; cond_then; cond_else; cond_if_assumes_false = false };
        }
  | Cond cond_stmt ->
      assert cond_stmt.cond_if_assumes_false;
      assert (
        Poly.(
          cond_stmt.cond_else.stmt_desc
          = Block { block_is_ghost = false; block_body = [] }));

      let* orig_map = Rewriter.current_user_state in

      let cond_test =
        Option.map
          ~f:(fun test -> Expr.alpha_renaming test subst_map)
          cond_stmt.cond_test
      in

      let* cond_then = rewrite_ssa_stmts cond_stmt.cond_then in
      let* cond_else = rewrite_ssa_stmts cond_stmt.cond_else in

      let* _ = Rewriter.set_user_state orig_map in

      Rewriter.return
        Stmt.
          {
            s with
            stmt_desc =
              Cond
                {
                  cond_test;
                  cond_then;
                  cond_else;
                  cond_if_assumes_false = true;
                };
          }
  | Loop loop_stmt -> assert false

let rewrite_ssa_transform (c : Callable.t) :
    (Callable.t, var_decl ident_map) Rewriter.t_ext =
  let open Rewriter.Syntax in
  match c.call_def with
  | FuncDef _ | ProcDef { proc_body = None } -> Rewriter.return c
  | ProcDef { proc_body = Some body } ->
      let init_map =
        List.fold
          (c.call_decl.call_decl_formals @ c.call_decl.call_decl_returns
         @ c.call_decl.call_decl_locals)
          ~init:(Map.empty (module Ident))
          ~f:(fun map var_decl ->
            Map.add_exn map ~key:var_decl.var_name ~data:var_decl)
      in

      let* _ = Rewriter.set_user_state init_map in

      Logs.debug (fun m ->
          m "Rewrites.rewrite_ssa_transform: Starting rewrites on callable %a"
            Callable.pr c);

      let+ body = rewrite_ssa_stmts body in

      { c with call_def = ProcDef { proc_body = Some body } }

let rec rewrite_assign_stmts (s : Stmt.t) : Stmt.t Rewriter.t =
  let open Rewriter.Syntax in
  Logs.debug (fun m ->
      m "Rewrites.rewrite_assign_stmts: Starting rewrites on statement %a"
        Stmt.pr s);

  match s.stmt_desc with
  | Basic (Assign assign_stmt) ->
      let assume_stmt =
        Stmt.mk_assume_expr ~loc:s.stmt_loc
          (Expr.mk_eq
             (Expr.mk_tuple assign_stmt.assign_lhs)
             assign_stmt.assign_rhs)
      in

      Rewriter.return assume_stmt
  | _ ->
      let* s = Rewriter.Stmt.descend s ~f:rewrite_assign_stmts in

      Rewriter.return s

let rec rewrites_phase_1 (m : Module.t) : Module.t Rewriter.t =
  let open Rewriter.Syntax in
  Logs.debug (fun m -> m "Rewrites.all_rewrites: Starting rewrites");

  Logs.debug (fun m1 ->
      m1
        "Rewrites.all_rewrites: Starting rewrite_callable_error_msg on module \
         %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_callables ~f:rewrite_callable_error_msg m in

  Logs.debug (fun m1 ->
      m1 "Rewrites.all_rewrites: Starting rewrite_compr_expr on module %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_expressions ~f:rewrite_compr_expr m in

  Logs.debug (fun m1 ->
      m1 "Rewrites.all_rewrites: Starting rewrite_set_diff_expr on module %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_expressions ~f:rewrite_set_diff_expr m in

  Logs.debug (fun m1 ->
      m1 "Rewrites.all_rewrites: Starting rewrite_loops on module %a" Ident.pr
        m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_stmts ~f:rewrite_loops m in

  Rewriter.return m

let rec rewrites_phase_2 (m : Module.t) : Module.t Rewriter.t =
  let open Rewriter.Syntax in
  Logs.debug (fun m1 ->
      m1
        "Rewrites.all_rewrites: Starting rewrite_atomic_callable_token on \
         module %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m =
    Rewriter.Module.rewrite_callables ~f:rewrite_atomic_callable_token m
  in

  Logs.debug (fun m1 ->
      m1 "Rewrites.all_rewrites: Starting rewrite_au_cmnds on module %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m =
    Rewriter.Module.rewrite_callables
      ~f:AtomicityAnalysis.rewrite_atomicity_analysis m
  in

  Logs.debug (fun m1 ->
      m1 "Rewrites.all_rewrites: Starting rewrite_cas on module %a" Ident.pr
        m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_stmts ~f:rewrite_cas_stmts m in

  Logs.debug (fun m1 ->
      m1
        "Rewrites.all_rewrites: Starting rewrite_fold_unfold_stmts on module %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_stmts ~f:rewrite_fold_unfold_stmts m in

  Logs.debug (fun m1 ->
      m1 "Rewrites.all_rewrites: Starting rewrite_call_stmts on module %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_stmts ~f:rewrite_call_stmts m in

  Logs.debug (fun m1 ->
      m1 "Rewrites.all_rewrites: Starting rewrite_ret_stmts on module %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_stmts ~f:rewrite_ret_stmts m in

  Logs.debug (fun m1 ->
      m1 "Rewrites.all_rewrites: Starting rewrite_frac_field_types on module %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rec_rewrite_symbols ~f:rewrite_frac_field_types m in

  Logs.debug (fun m1 ->
      m1 "Rewrites.all_rewrites: Starting rewrite_own_expr_4_arg on module %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_expressions ~f:rewrite_own_expr_4_arg m in

  Logs.debug (fun m1 ->
      m1
        "Rewrites.all_rewrites: Starting rewrite_new_fpu_stmt_heap_arg on \
         module %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_stmts ~f:rewrite_new_fpu_stmt_heap_arg m in

  Logs.debug (fun m1 ->
      m1 "Rewrites.all_rewrites: Starting rewrite_new_stmts on module %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_stmts ~f:rewrite_new_stmts m in

  Logs.debug (fun m1 ->
      m1
        "Rewrites.all_rewrites: Starting rewrite_add_predicate_validity_lemmas \
         on module %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m =
    Rewriter.Module.rewrite_callables ~f:rewrite_add_predicate_validity_lemmas m
  in

  Logs.debug (fun m1 ->
      m1
        "Rewrites.all_rewrites: Starting rewrite_callable_pre_post_conds on \
         module %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m =
    Rewriter.Module.rewrite_callables ~f:rewrite_callable_pre_post_conds m
  in

  Logs.debug (fun m1 ->
      m1 "Rewrites.all_rewrites: Starting rewrite_add_field_utils on module %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m =
    Rewriter.Module.rec_rewrite_symbols
      ~f:HeapsExplicitTrnsl.rewrite_add_field_utils m
  in

  Logs.debug (fun m1 ->
      m1 "Rewrites.all_rewrites: Starting rewrite_add_pred_utils on module %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m =
    Rewriter.Module.rewrite_callables
      ~f:HeapsExplicitTrnsl.rewrite_add_pred_utils m
  in

  Logs.debug (fun m1 ->
      m1
        "Rewrites.all_rewrites: Starting rewrite_add_atomics_utils on module %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m =
    Rewriter.Module.rewrite_callables
      ~f:HeapsExplicitTrnsl.rewrite_add_atomics_utils m
  in

  Logs.debug (fun m1 ->
      m1
        "Rewrites.all_rewrites: Starting rewriter_skolemize_inhale_stmts on \
         module %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m =
    Rewriter.Module.rewrite_stmts
      ~f:HeapsExplicitTrnsl.TrnslInhale.rewriter_skolemize_inhale_stmts m
  in

  Logs.debug (fun m1 ->
      m1
        "Rewrites.all_rewrites: Starting \
         rewriter_user_annot_elim_exists_from_exhales on module %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m =
    Rewriter.eval_with_user_state ~init:None
      (Rewriter.Module.rewrite_stmts
         ~f:
           HeapsExplicitTrnsl.TrnslExhale
           .rewriter_user_annot_elim_exists_from_exhales m)
  in

  Logs.debug (fun m1 ->
      m1 "Rewrites.all_rewrites: Starting rewrite_introduce_heaps on module %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_callables ~f:rewrite_introduce_heaps m in

  Logs.debug (fun m1 ->
      m1
        "Rewrites.all_rewrites: Starting rewriter_eliminate_binds_for_inhale \
         on module %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m =
    Rewriter.eval_with_user_state ~init:None
      (Rewriter.Module.rewrite_stmts
         ~f:HeapsExplicitTrnsl.TrnslInhale.rewriter_eliminate_binds_for_inhale m)
  in

  let* m = Rewriter.Module.rewrite_stmts ~f:HeapsExplicitTrnsl.rewrite_fpu m in

  let* m =
    Rewriter.Module.rewrite_stmts ~f:HeapsExplicitTrnsl.rewrite_binds m
  in

  Logs.debug (fun m1 ->
      m1
        "Rewrites.all_rewrites: Starting \
         rewriter_find_witness_elim_exists_from_exhale on module %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m =
    Rewriter.Module.rewrite_stmts
      ~f:
        HeapsExplicitTrnsl.TrnslExhale
        .rewriter_find_witness_elim_exists_from_exhale m
  in

  Logs.debug (fun m1 ->
      m1
        "Rewrites.all_rewrites: Starting rewrite_make_heaps_explicit on module \
         %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m =
    Rewriter.Module.rewrite_stmts
      ~f:HeapsExplicitTrnsl.rewrite_make_heaps_explicit m
  in

  let* m = Rewriter.Module.rewrite_types ~f:rewrite_expand_types m in

  Logs.debug (fun m1 ->
      m1
        "Rewrites.all_rewrites: Starting rewrite_ssa_transform on module %a: %a"
        Ident.pr m.mod_decl.mod_decl_name Module.pr m);
  let* m =
    Rewriter.eval_with_user_state
      ~init:(Map.empty (module Ident))
      (Rewriter.Module.rewrite_callables ~f:rewrite_ssa_transform m)
  in

  Logs.debug (fun m1 ->
      m1 "Rewrites.all_rewrites: Starting rewrite_assign_stmts on module %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_stmts ~f:rewrite_assign_stmts m in

  let* tbl = Rewriter.get_table in

  (* Logs.debug (fun m -> m "Rewrites.all_rewrites: SymbolTbl Symbols: \n%a\n" (Util.Print.pr_list_comma (fun ppf (k,v) -> Stdlib.Format.fprintf ppf "%a -> %a" QualIdent.pr k Module.pr_symbol v)) (Map.to_alist (Map.filter_keys tbl.tbl_symbols ~f:(fun k -> Poly.((QualIdent.to_string k) = "$Program.pr"))))); *)
  Rewriter.return m

let process_module ?(tbl = SymbolTbl.create ()) (m : Module.t) =
  assert (SymbolTbl.curr_is_root tbl);

  (* assert Ident.(m.mod_decl.mod_decl_name = QualIdent.to_ident (SymbolTbl.root_ident tbl)); *)
  let tbl, m = Rewriter.eval (rewrites_phase_1 m) tbl in

  let tbl, m = Rewriter.eval (Masks.compute_masks m) tbl in

  let tbl, m = Rewriter.eval (rewrites_phase_2 m) tbl in

  (tbl, m)
