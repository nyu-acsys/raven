open Base
open Ast
open Util

let rec rewrite_compr_expr (expr: expr) : expr Rewriter.t =
  let open Rewriter.Syntax in
  match expr with
  | Binder (Compr, v_l, trgs, inner_expr, _expr_attr) ->
    let* _ = Rewriter.add_locals v_l
    and* inner_expr = rewrite_compr_expr inner_expr in
        
    let compr_fn_ident = Ident.fresh (Expr.to_loc expr) "compr" in

    let free_vars = Expr.signature inner_expr in
    let free_vars = Map.filter_keys free_vars ~f:(fun qual_ident -> not (List.exists v_l ~f:(fun v_l -> Poly.((QualIdent.from_ident v_l.var_name) = qual_ident)))) in
    
    let formal_var_decls, actual_arg_exprs =
      Map.fold free_vars ~init:([], []) ~f:(fun ~key ~data (formals, actuals) ->
          if QualIdent.is_qualified key then formals, actuals else
            { Type.var_name = QualIdent.unqualify key;
              var_loc = Expr.to_loc inner_expr;
              var_type = data;
              var_const = true;
              var_ghost = false;
              var_implicit = false;
            } :: formals,
            Expr.mk_var ~loc:(Expr.to_loc inner_expr) ~typ:data key :: actuals
      )
    in

    let ret_var_decl = 
      { Type.var_name = Ident.fresh (Expr.to_loc expr) "ret";
        var_loc = Expr.to_loc expr;
        var_type = Expr.to_type expr;
        var_const = false;
        var_ghost = false;
        var_implicit = false;
      } 
    in

    let ret_typ = (Expr.to_type expr) in
    
    let postcond = 
      let spec_form =
        if Type.is_set ret_typ then
          
          let var_decl = List.hd_exn v_l in
          
          Expr.mk_binder ~typ:Type.bool Forall [var_decl] (
            Expr.mk_and [
              Expr.mk_app ~typ:Type.bool Impl [
                inner_expr;
                
                Expr.mk_app ~typ:Type.bool Elem [ 
                  Expr.from_var_decl var_decl;
                  Expr.from_var_decl ret_var_decl
                ];
              ]; 
              Expr.mk_app ~typ:Type.bool Impl [
                Expr.mk_app ~typ:Type.bool Elem [ 
                  Expr.from_var_decl var_decl;
                  Expr.from_var_decl ret_var_decl
                ];
                
                inner_expr;
              ]
            ]
          )
            
        else 
          (* Type.is_map ret_typ *)
          let var_decl = List.hd_exn v_l in
          
          Expr.mk_binder ~typ:Type.bool Forall [var_decl] 
            (Expr.mk_app ~typ:Type.bool Eq
               [ inner_expr;
                 
                 Expr.mk_app ~typ:(Type.map_codom ret_typ) MapLookUp [ 
                   Expr.from_var_decl ret_var_decl;
                   Expr.from_var_decl var_decl ]
               ]
            )

      in
      
      Stmt.mk_spec spec_form
      
    in

    let call_decl = {
      Callable.call_decl_kind = Func;
      call_decl_name = compr_fn_ident;
      call_decl_formals = formal_var_decls;
      call_decl_returns = [ret_var_decl];
      call_decl_locals = [];
      call_decl_precond = [];
      call_decl_postcond = [postcond];
      call_decl_is_free = true;
      call_decl_is_auto = false;
      call_decl_loc = Expr.to_loc expr;
    }
      
    in

    let* current_module_name = Rewriter.current_module_name in
    let compr_fn_qual_ident = QualIdent.append current_module_name compr_fn_ident in
    let compr_fn_def = Module.CallDef (Callable.{ call_decl; call_def = FuncDef { func_body = None;} }) in

    Logs.debug (fun m -> m "Rewrites.rewrite_compr_expr: compr_fn: %a" Symbol.pr compr_fn_def);
    
    let new_expr = 
      Expr.mk_app ~typ:(ret_typ) ~loc:(Expr.to_loc expr) (Expr.Var compr_fn_qual_ident) actual_arg_exprs
    in

    (* TODO: Change Rewriter.introduce_symbol to Rewriter.introduce_typecheck_symbol *)
    let+ _ = Rewriter.introduce_symbol compr_fn_def in
    new_expr
      
  | _ -> Rewriter.Expr.descend expr ~f:rewrite_compr_expr

let rec rewrite_set_diff_expr (expr: expr) : expr Rewriter.t =
  let open Rewriter.Syntax in
  match expr with
  | App (Diff, [expr1; expr2], _expr_attr) ->
    Logs.debug (fun m -> m "Rewrites.rewrite_set_diff_expr: expr: %a" Expr.pr expr);
      
    let set_element_type = Type.set_elem (Expr.to_type expr1) in
    let typ_string = Rewriter.ProgUtils.serialize (Type.to_string set_element_type) in

    let set_diff_fn_ident = Ident.fresh (Expr.to_loc expr) (Stdlib.Format.asprintf "set_diff$%s" typ_string) in

    (* let free_vars = Expr.signature inner_expr in *)
    
    let var_decl1 = 
      { Type.var_name = Ident.fresh (Expr.to_loc expr) "a";
        var_loc = Expr.to_loc expr;
        var_type = (Expr.to_type expr1);
        var_const = true;
        var_ghost = false;
        var_implicit = false;
      } 
    in

    let var_decl2 = 
      { Type.var_name = Ident.fresh (Expr.to_loc expr) "b";
        var_loc = Expr.to_loc expr;
        var_type = (Expr.to_type expr1);
        var_const = true;
        var_ghost = false;
        var_implicit = false;
      } 
    in


    let formal_var_decls, actual_arg_exprs =
      [var_decl1; var_decl2], [expr1; expr2]
      
    in

    let ret_var_decl = 
      { Type.var_name = Ident.fresh (Expr.to_loc expr) "ret";
        var_loc = Expr.to_loc expr;
        var_type = Expr.to_type expr;
        var_const = false;
        var_ghost = false;
        var_implicit = false;
      } 
    in

    let ret_typ = (Expr.to_type expr) in
    
    let postcond = 
      let spec_form =
          
        let var_decl = {
          Type.var_name = Ident.fresh (Expr.to_loc expr) "x";
          var_loc = Expr.to_loc expr;
          var_type = set_element_type;
          var_const = true;
          var_ghost = false;
          var_implicit = false;
        } in
        
        Expr.mk_binder ~typ:Type.bool Forall [var_decl] ( (* forall x :: *)
          Expr.mk_and [
            Expr.mk_app ~typ:Type.bool Impl [ (*    x \in a && !(x \in b)   ==>    x \in ret  *)
              Expr.mk_and [
                Expr.mk_app ~typ:Type.bool Elem [ 
                  Expr.from_var_decl var_decl;
                  Expr.from_var_decl var_decl1
                ];
                Expr.mk_not (Expr.mk_app ~typ:Type.bool Elem [ 
                  Expr.from_var_decl var_decl;
                  Expr.from_var_decl var_decl2
                ];)
              ];
              
              Expr.mk_app ~typ:Type.bool Elem [ 
                Expr.from_var_decl var_decl;
                Expr.from_var_decl ret_var_decl
              ];
            ];

            Expr.mk_app ~typ:Type.bool Impl [ (*    x \in ret    ==>    x \in a && !(x \in b)  *)              
              Expr.mk_app ~typ:Type.bool Elem [ 
                Expr.from_var_decl var_decl;
                Expr.from_var_decl ret_var_decl
              ];

              Expr.mk_and [
                Expr.mk_app ~typ:Type.bool Elem [ 
                  Expr.from_var_decl var_decl;
                  Expr.from_var_decl var_decl1
                ];
                Expr.mk_not (Expr.mk_app ~typ:Type.bool Elem [ 
                  Expr.from_var_decl var_decl;
                  Expr.from_var_decl var_decl2
                ];)
              ];

            ]
          ]
        )
      in
      
      Stmt.mk_spec spec_form
      
    in

    let call_decl = {
      Callable.call_decl_kind = Func;
      call_decl_name = set_diff_fn_ident;
      call_decl_formals = formal_var_decls;
      call_decl_returns = [ret_var_decl];
      call_decl_locals = [];
      call_decl_precond = [];
      call_decl_postcond = [postcond];
      call_decl_is_free = true;
      call_decl_is_auto = false;
      call_decl_loc = Expr.to_loc expr;
    }
      
    in

    let* current_module_name = Rewriter.current_module_name in

    let set_diff_fn_qual_ident = QualIdent.append current_module_name set_diff_fn_ident in
    let set_diff_fn_def = Module.CallDef (Callable.{ call_decl; call_def = FuncDef { func_body = None;} }) in
    
    let new_expr = 
      Expr.mk_app ~typ:ret_typ ~loc:(Expr.to_loc expr) (Expr.Var set_diff_fn_qual_ident) actual_arg_exprs
    in

    (* TODO: Change Rewriter.introduce_symbol to Rewriter.introduce_typecheck_symbol *)
    let+ _ = Rewriter.introduce_typecheck_symbol ~loc:(Expr.to_loc expr) ~f:Typing.process_symbol set_diff_fn_def in
    new_expr
      
  | _ -> Rewriter.Expr.descend expr ~f:rewrite_set_diff_expr

let rewrite_compr_modules (tbl: SymbolTbl.t) (m: Module.t) =
  Rewriter.eval (Rewriter.Module.rewrite_expressions ~f:rewrite_compr_expr m) tbl



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
let rec rewrite_loops (stmt: Stmt.t) : Stmt.t Rewriter.t =
  let open Rewriter.Syntax in
  match stmt.stmt_desc with
  | Loop loop ->    
    Logs.debug (fun m -> m "Rewrites.rewrite_loops: loop: %a" Stmt.pr stmt); 
  
    let* loop_arg_var_decls, loop_arg_renaming_map, loop_arg_renaming_qual_ident_map, curr_loop_arg_var_decls = 
      begin
        (* Local variables accessed from loop body become arguments for loop procedure *)
        let curr_loop_args = Stmt.local_vars_accessed loop.loop_postbody |> Set.to_list in
        let+ curr_loop_arg_var_decls = Rewriter.List.map curr_loop_args ~f:(fun var -> 
          let+ symbol = Rewriter.find_and_reify var.ident_loc (QualIdent.from_ident var) in
          
          (match symbol with
          | VarDef v -> v.var_decl
          | _ -> Error.error stmt.stmt_loc ("Expected a variable (1); found " ^ (Symbol.to_string symbol) ^ " for var: " ^ (Ident.to_string var)))
        ) in
      
        (* redefined loop_args for uniqueness *)
        let loop_arg_var_decls = List.map curr_loop_arg_var_decls ~f:(fun var_decl -> 
          let new_var_name = Ident.fresh stmt.stmt_loc var_decl.var_name.ident_name in
          Logs.debug (fun m -> m "Loop old_var_name: %a" Ident.pr var_decl.var_name);
          Logs.debug (fun m -> m "Loop new_var_name: %a" Ident.pr new_var_name);
          let new_new_var_name = Ident.fresh stmt.stmt_loc var_decl.var_name.ident_name in
          Logs.debug (fun m -> m "Loop new_new_var_name: %a" Ident.pr new_new_var_name);
          { var_decl with var_name = new_var_name }
          (* { var_decl with var_name = Ident.fresh stmt.stmt_loc var_decl.var_name.ident_name } *)
        ) in

        Logs.debug (fun m -> m "Loop curr_loop_arg_var_decls:\n %a" (Print.pr_list_comma Ident.pr) (List.map curr_loop_arg_var_decls ~f:(fun var_decl -> var_decl.var_name)));

        Logs.debug (fun m -> m "Loop loop_arg_var_decls:\n %a" (Print.pr_list_comma Ident.pr) (List.map loop_arg_var_decls ~f:(fun var_decl -> var_decl.var_name)));

        let loop_arg_renaming_map = List.fold2_exn curr_loop_arg_var_decls loop_arg_var_decls ~init:(Map.empty (module QualIdent)) ~f:(fun map old_var_decl new_var_decl ->
          Map.add_exn map ~key:(QualIdent.from_ident old_var_decl.var_name) ~data:(Expr.from_var_decl new_var_decl)
        ) in

        let loop_arg_renaming_qual_ident_map = List.fold2_exn curr_loop_arg_var_decls loop_arg_var_decls ~init:(Map.empty (module QualIdent)) ~f:(fun map old_var_decl new_var_decl ->
          Map.add_exn map ~key:(QualIdent.from_ident old_var_decl.var_name) ~data:(QualIdent.from_ident new_var_decl.var_name)
        ) in
        
        loop_arg_var_decls, loop_arg_renaming_map, loop_arg_renaming_qual_ident_map, curr_loop_arg_var_decls
      end 
    in

    let* loop_ret_var_decls, loop_ret_renaming_map, curr_loop_ret_var_decls =
      begin
        (* Local variables modified from loop body become ret vals for loop procedure *)
        let curr_loop_rets = Stmt.stmt_local_vars_modified loop.loop_postbody in
        let+ curr_loop_ret_var_decls = Rewriter.List.map curr_loop_rets ~f:(fun var -> 
          let+ symbol = Rewriter.find_and_reify stmt.stmt_loc (QualIdent.from_ident var) in
          
          (match symbol with
          | VarDef v -> v.var_decl
          | _ -> Error.error stmt.stmt_loc ("Expected a variable (2); found " ^ (Symbol.to_string symbol)))
          ) in

        (* redefined loop_rets for uniqueness *)
        let loop_ret_var_decls = List.map curr_loop_ret_var_decls ~f:(fun var_decl -> 
          { var_decl with var_name = Ident.fresh stmt.stmt_loc var_decl.var_name.ident_name }
        ) in

        let loop_ret_renaming_map = List.fold2_exn curr_loop_ret_var_decls loop_ret_var_decls ~init:(Map.empty (module QualIdent)) ~f:(fun map old_var_decl new_var_decl ->
          Map.add_exn map ~key:(QualIdent.from_ident old_var_decl.var_name) ~data:(Expr.from_var_decl new_var_decl)
        ) in

        loop_ret_var_decls, loop_ret_renaming_map, curr_loop_ret_var_decls
      end
    in
    
    let* loop_proc_name = 
      let+ proc_name = Rewriter.current_scope_id in  
      Ident.fresh stmt.stmt_loc (proc_name.qual_base.ident_name ^ "_loop") 
    in

    (* Create new map which replaces loop_arg vars with loop_ret vars, for post conditions *)
    let loop_post_vars_renaming_map = Map.fold loop_ret_renaming_map ~init:loop_arg_renaming_map ~f:(fun ~key ~data map ->
      Map.set map ~key ~data
    ) in

    let new_proc_decl = 
      let loop_precond = List.map loop.loop_contract ~f:(fun spec -> { spec with spec_form = Expr.alpha_renaming spec.spec_form loop_arg_renaming_map}) in

      let loop_postcond = List.map loop.loop_contract ~f:(fun spec -> { spec with spec_form = Expr.alpha_renaming spec.spec_form loop_post_vars_renaming_map}) in

      (* Adding negation of loop_cond to postconditions *)
      let loop_postcond = loop_postcond @ [Stmt.mk_spec (Expr.mk_not ~loc:stmt.stmt_loc (Expr.alpha_renaming loop.loop_test loop_post_vars_renaming_map))] in

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
        call_decl_loc = stmt.stmt_loc;
      }
    in

    let* loop_body =
      begin
        let set_ret_vals_to_initial_args = List.map (Map.to_alist loop_ret_renaming_map) ~f:(fun (old_var, new_expr) ->
          Stmt.mk_assign ~loc:(Stmt.loc stmt) [new_expr] (Map.find_exn loop_arg_renaming_map old_var)
        ) in

        let recurse_call =
          let lhs_list = List.map loop_ret_var_decls ~f:(fun var_decl -> QualIdent.from_ident var_decl.var_name) in

          let args_list = List.map loop_arg_var_decls ~f:(fun var_decl -> Expr.from_var_decl var_decl) in

          Stmt.mk_call ~loc:(Stmt.loc stmt) ~lhs:lhs_list (QualIdent.from_ident loop_proc_name) args_list in

        (* TODO: Rename variables from curr_vars to loop_vars in loop body *)
        let* loop_body = Rewriter.Stmt.rewrite_qual_idents  loop.loop_postbody ~f:(fun qual_ident -> 
          Option.value (Map.find loop_arg_renaming_qual_ident_map qual_ident) ~default:qual_ident
        ) in

        let cond_stmt = 
          let test = (Expr.alpha_renaming loop.loop_test loop_arg_renaming_map) in
          let then_stmt = Stmt.mk_block_stmt ~loc:(Stmt.loc stmt) [loop_body; recurse_call] in
          let else_stmt = Stmt.mk_skip ~loc:(Stmt.loc stmt) in
          
          Stmt.mk_cond ~loc:(Stmt.loc stmt) test then_stmt else_stmt 
        in

        let ret_stmt = 
          let ret_tuple = Expr.mk_tuple ~loc:stmt.stmt_loc (List.map loop_ret_var_decls ~f:(fun var_decl -> Expr.from_var_decl var_decl)) in

          Stmt.mk_return ~loc:stmt.stmt_loc ret_tuple 
        in

        Rewriter.return (Stmt.mk_block_stmt ~loc:stmt.stmt_loc (set_ret_vals_to_initial_args @ [cond_stmt; ret_stmt]))
      end
    in

    let loop_proc_symbol =
      let call_def = Callable.{ call_decl = new_proc_decl; call_def = ProcDef { proc_body = Some loop_body; } } in
      Module.CallDef call_def

    in


    Logs.debug (fun m -> m "Rewrites.rewrite_loops: Pre-typecheck loop_proc_symbol:\n %a" Symbol.pr loop_proc_symbol);

    let* _ = Rewriter.introduce_typecheck_symbol ~loc:stmt.stmt_loc ~f:Typing.process_symbol loop_proc_symbol in

    let* curr_state = Rewriter.__get_state in

    Logs.debug (fun m -> m "Rewrites.rewrite_loops: Loop introduced symbols:\n %a" (Print.pr_list_comma Symbol.pr) (List.hd_exn curr_state.state_new_symbols));

    Logs.debug (fun m -> m "Rewrites.rewrite_loops: Loop curr_scope:\n %a" QualIdent.pr curr_state.state_table.tbl_curr.scope_id);


    let new_stmt = 
      let lhs_list = List.map curr_loop_ret_var_decls ~f:(fun var_decl -> QualIdent.from_ident var_decl.var_name) in
      let args_list = List.map curr_loop_arg_var_decls ~f:(fun var_decl -> Expr.from_var_decl var_decl) in

      Stmt.mk_call ~loc:(Stmt.loc stmt) ~lhs:lhs_list (QualIdent.from_ident loop_proc_name) args_list in


    Logs.debug (fun m -> m "Loop new_stmt:\n %a" Stmt.pr new_stmt);
    Rewriter.return new_stmt



  | _ -> Rewriter.Stmt.descend stmt ~f:rewrite_loops




let rec rewrite_ret_stmts (stmt: Stmt.t) : Stmt.t Rewriter.t =
  let open Rewriter.Syntax in
  match stmt.stmt_desc with
  | Basic (Return ret_expr) ->

    let* curr_proc_name = Rewriter.current_scope_id in

    let* callable_decl =
      Logs.debug (fun m -> m "Rewrites.rewrite_ret_stmts: curr_proc_name: %a" QualIdent.pr curr_proc_name);

      let+ symbol = Rewriter.find_and_reify stmt.stmt_loc curr_proc_name in
          
      (match symbol with
      | CallDef c -> 
        Logs.debug (fun m -> m "Rewrites.rewrite_ret_stmts: curr_proc: %a" Callable.pr c);      
        c.call_decl
      | _ -> Error.error stmt.stmt_loc "Expected a call_def")
    
    in

    let ret_expr_list = Expr.unfold_tuple ret_expr in

    let renaming_map = List.fold2_exn callable_decl.call_decl_returns ret_expr_list ~init:(Map.empty (module QualIdent)) ~f:(fun map var_decl expr ->
      Map.add_exn map ~key:(QualIdent.from_ident var_decl.var_name) ~data:expr
    ) in

    let postconds_spec = callable_decl.call_decl_postcond in

    let postconds_exhale_stmts = 
      if Callable.is_atomic callable_decl then
        let atomic_token_var = Expr.mk_var ~loc:(Stmt.loc stmt) ~typ:Type.atomic_token (QualIdent.from_ident (Rewriter.ProgUtils.callable_au_token_ident ~loc:(Stmt.loc stmt) callable_decl.call_decl_name)) in

        let concrete_args = List.filter callable_decl.call_decl_formals ~f:(fun var_decl -> not var_decl.var_implicit) in
        let concrete_args_expr = List.map concrete_args ~f:(Expr.from_var_decl) in
        
        [Stmt.mk_exhale_expr ~cmnt:(Some "au_return_stmt") ~loc:(Stmt.loc stmt) (Expr.mk_app ~loc:(Stmt.loc stmt) ~typ:Type.perm (Expr.AUPredCommit curr_proc_name) ((atomic_token_var :: concrete_args_expr) @ [ret_expr]))]

      else
      
        List.map postconds_spec ~f:(fun spec ->
        let expr = Expr.alpha_renaming spec.spec_form renaming_map in
        
        Stmt.mk_exhale_expr ~loc:stmt.stmt_loc ~cmnt:(Some ("postconds added for ret_stmt: " ^ Stmt.to_string stmt)) expr) 
    in

    let assume_false = Stmt.mk_assume_expr ~loc:stmt.stmt_loc (Expr.mk_bool ~loc:stmt.stmt_loc false) in

    let new_stmt = Stmt.mk_block_stmt ~loc:stmt.stmt_loc (postconds_exhale_stmts @ [assume_false]) in

    Rewriter.return new_stmt


  | _ -> Rewriter.Stmt.descend stmt ~f:rewrite_ret_stmts


let rec rewrite_new_stmts (stmt: Stmt.t) : Stmt.t Rewriter.t =
  let open Rewriter.Syntax in
  match stmt.stmt_desc with
  | Basic (New new_desc) ->
    Logs.debug (fun m -> m "Rewrites.rewrite_new_stmts: new_desc: %a" Stmt.pr stmt);

    let* new_stmts = Rewriter.List.map new_desc.new_args ~f:(fun (field_name, expr_optn) ->

    let* field_val = match expr_optn with
    | Some expr -> Rewriter.return expr
    | None -> Rewriter.ProgUtils.get_field_utils_id stmt.stmt_loc field_name

    in

    let* field_type = 
      let* field_symbol = Rewriter.find_and_reify stmt.stmt_loc field_name in
      match field_symbol with
      | FieldDef f -> Rewriter.return f.field_type
      | _ -> Error.error stmt.stmt_loc "Expected a field_def"

    in

    let inhale_expr = Expr.mk_app ~typ:Type.perm ~loc:stmt.stmt_loc Expr.Own 
      [Expr.mk_var ~loc:stmt.stmt_loc ~typ:Type.ref new_desc.new_lhs;
      Expr.mk_var ~loc:stmt.stmt_loc ~typ:field_type field_name;
      field_val;
      ]
    in

    let inhale_stmt = Stmt.mk_inhale_expr ~cmnt:(Some ("new stmt: " ^ Stmt.to_string stmt)) ~loc:stmt.stmt_loc inhale_expr in

    Rewriter.return inhale_stmt
      
    )

    in

    Rewriter.return (Stmt.mk_block_stmt ~loc:stmt.stmt_loc new_stmts)



  | _ -> Rewriter.Stmt.descend stmt ~f:rewrite_new_stmts


(** Replaces a `fold p(x, y)` stmt with `exhale p(); inhale p.body`. Need to ensure that atomicity checks have been done before calling this rewrite *)
let rec rewrite_fold_unfold_stmts (stmt: Stmt.t) : Stmt.t Rewriter.t =
  let open Rewriter.Syntax in
  match stmt.stmt_desc with
  | Basic (Use use_desc) ->
    assert (match use_desc.use_kind with 
      | Fold | Unfold -> true 
      | _ -> false
    );

    let* symbol = Rewriter.find_and_reify stmt.stmt_loc use_desc.use_name in

    let pred_decl, body = (match symbol with
      | CallDef c -> 
        let spec = (match c.call_def with
          | ProcDef p -> Error.error stmt.stmt_loc "Expected a func_def inside a fold/unfold stmt"        
          | FuncDef { func_body = None} -> Error.error stmt.stmt_loc "Empty func_def body inside a fold/unfold stmt not allowed"
          | FuncDef { func_body = Some e} -> e
        ) in

        c.call_decl, spec

      | _ -> Error.error stmt.stmt_loc "Expected a call_def"
    ) in 

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

      let renaming_map = List.fold2_exn (pred_decl.call_decl_formals @ pred_decl.call_decl_returns) (use_desc.use_args) ~init:(Map.empty (module QualIdent)) ~f:(fun map var_decl arg_expr -> Map.add_exn map ~key:(QualIdent.from_ident var_decl.var_name) ~data:arg_expr) in

      (* renaming_map, fresh_dropped_args *)
      renaming_map, ()
    in
    
    let body_expr = 
      let new_body = Expr.alpha_renaming body renaming_map in
      
      (* Expr.mk_binder ~loc:stmt.stmt_loc ~typ:Type.bool Exists fresh_dropped_args new_body  *)
      new_body
    in

    let pred_expr = Expr.mk_app ~loc:stmt.stmt_loc ~typ:Type.bool (Expr.Var use_desc.use_name) use_desc.use_args in

    let new_stmt = 
      let inhale_stmt, exhale_stmt =
        match use_desc.use_kind with
        | Fold -> 
          Stmt.mk_inhale_expr ~loc:stmt.stmt_loc ~cmnt:(Some ("fold : " ^ Expr.to_string pred_expr)) pred_expr, 
          Stmt.mk_exhale_expr ~loc:stmt.stmt_loc ~cmnt:(Some ("fold : " ^ Expr.to_string pred_expr)) body_expr
        | Unfold -> 
          Stmt.mk_inhale_expr ~loc:stmt.stmt_loc ~cmnt:(Some ("unfold : " ^ Expr.to_string pred_expr)) body_expr,
          Stmt.mk_exhale_expr ~loc:stmt.stmt_loc ~cmnt:(Some ("unfold : " ^ Expr.to_string pred_expr)) pred_expr 

        | _ -> assert false
      in

      Stmt.mk_block_stmt ~loc:stmt.stmt_loc [exhale_stmt; inhale_stmt]

    in

    Rewriter.return new_stmt
    

  | _ -> Rewriter.Stmt.descend stmt ~f:rewrite_fold_unfold_stmts

let rec rewrite_call_stmts (stmt: Stmt.t) : Stmt.t Rewriter.t =
  let open Rewriter.Syntax in
  match stmt.stmt_desc with
  | Basic (Call call_desc) ->
    let* symbol = Rewriter.find_and_reify stmt.stmt_loc call_desc.call_name in

    let call_decl, call_def = (match symbol with
      | CallDef c -> c.call_decl, c.call_def
      | _ -> Error.error stmt.stmt_loc "Expected a call_def"
    ) in

    let* lhs_list = Rewriter.List.map call_desc.call_lhs ~f:(fun qual_iden -> 
      let* symbol = Rewriter.find_and_reify stmt.stmt_loc qual_iden in
      
      match symbol with
      | VarDef v -> Rewriter.return (Expr.from_var_decl v.var_decl)
      | _ -> Error.error stmt.stmt_loc ("Expected a variable (3); found " ^ (Symbol.to_string symbol))
    ) in

    let* quant_renaming_map, quant_dropped_args, new_renaming_map, new_dropped_args = 
      let truncated_formal_args, dropped_formal_args = List.split_n call_decl.call_decl_formals (List.length call_desc.call_args) in

      let fresh_dropped_args = List.map dropped_formal_args ~f:(fun var_decl -> 
        { var_decl with var_name = Ident.fresh stmt.stmt_loc var_decl.var_name.ident_name; var_loc = stmt.stmt_loc; }
      ) in

      let fresh_dropped_args_exprs = List.map fresh_dropped_args ~f:(Expr.from_var_decl) in

      (* Need to ensure that call_decl_returns and call_desc.call_lhs line up *)
      
      let renaming_map = List.fold2_exn (truncated_formal_args @ dropped_formal_args @ call_decl.call_decl_returns) (call_desc.call_args @ fresh_dropped_args_exprs @ lhs_list) ~init:((Map.empty (module QualIdent))) ~f:(fun map var_decl arg_expr ->
        Map.add_exn map ~key:(QualIdent.from_ident var_decl.var_name) ~data:arg_expr
      )
      in

      let fresh_dropped_args2 = List.map dropped_formal_args ~f:(fun var_decl -> 
        { var_decl with var_name = Ident.fresh stmt.stmt_loc var_decl.var_name.ident_name; var_loc = stmt.stmt_loc; }
      ) in

      let fresh_dropped_args2_exprs = List.map fresh_dropped_args2 ~f:(Expr.from_var_decl) in

      (* Need to ensure that call_decl_returns and call_desc.call_lhs line up *)
      
      let renaming_map2 = List.fold2_exn (truncated_formal_args @ dropped_formal_args @ call_decl.call_decl_returns) (call_desc.call_args @ fresh_dropped_args2_exprs @ lhs_list) ~init:((Map.empty (module QualIdent))) ~f:(fun map var_decl arg_expr ->
        Map.add_exn map ~key:(QualIdent.from_ident var_decl.var_name) ~data:arg_expr
      )
      in

      Rewriter.return (renaming_map, fresh_dropped_args, renaming_map2, fresh_dropped_args2)
    in

    (match call_def with
    | ProcDef _ -> 
      let* _ = Rewriter.List.map new_dropped_args ~f:(fun var -> 
        Rewriter.introduce_symbol (Module.VarDef { var_decl = var; var_init = None; })
      ) in
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

      let assert_stmt = Stmt.mk_assert_expr ~loc:stmt.stmt_loc ~cmnt:(Some ("Assert stmt for Call: " ^ Stmt.to_string stmt)) 
        (Expr.mk_binder ~loc:stmt.stmt_loc Exists quant_dropped_args (Expr.mk_and (List.map call_decl.call_decl_precond ~f:(fun spec -> Expr.alpha_renaming spec.spec_form quant_renaming_map) ))) in

      let assume_stmt = Stmt.mk_assume_expr ~loc:stmt.stmt_loc ~cmnt:(Some ("Assume stmt for Call: " ^ Stmt.to_string stmt)) 
        (Expr.mk_and (List.map call_decl.call_decl_precond ~f:(fun spec -> Expr.alpha_renaming spec.spec_form new_renaming_map) )) in

      let exhale_stmt = Stmt.mk_exhale_expr ~loc:stmt.stmt_loc ~cmnt:(Some ("Exhale stmt for Call: " ^ Stmt.to_string stmt)) 
        (Expr.mk_and (List.map call_decl.call_decl_precond ~f:(fun spec -> Expr.alpha_renaming spec.spec_form new_renaming_map) )) in

      let inhale_stmt = Stmt.mk_inhale_expr ~loc:stmt.stmt_loc ~cmnt:(Some ("Inhale stmt for Call: " ^ Stmt.to_string stmt)) 
        (Expr.mk_and (List.map call_decl.call_decl_postcond ~f:(fun spec -> Expr.alpha_renaming spec.spec_form new_renaming_map) )) in

      (* TODO: Need to havoc ret vars before inhaling postconditions *)
      let new_stmt = Stmt.mk_block_stmt ~loc:stmt.stmt_loc 
        (* (if (List.is_empty call_decl.call_decl_precond ) then *)
          (* [inhale_stmt] *)
        (* else *)
          (if (List.is_empty new_dropped_args) then 
            [exhale_stmt; inhale_stmt]
          else
            [assert_stmt; assume_stmt; exhale_stmt; inhale_stmt]
          (* ) *)
        ) in
      
      Rewriter.return new_stmt

    | FuncDef _ -> 
      let exhale_stmts = List.map call_decl.call_decl_precond ~f:(fun spec -> Stmt.mk_exhale_spec ~cmnt:(Some ("Call: " ^ Stmt.to_string stmt)) ~loc:stmt.stmt_loc spec) in

      let ret_typ = Type.mk_prod stmt.stmt_loc (List.map call_decl.call_decl_returns ~f:(fun var_decl -> var_decl.var_type)) in

      let new_assign_stmt = Stmt.mk_assign ~loc:stmt.stmt_loc lhs_list (Expr.mk_app ~loc:stmt.stmt_loc ~typ:ret_typ (Expr.Var call_desc.call_name) call_desc.call_args) in

      let new_stmt = Stmt.mk_block_stmt ~loc:stmt.stmt_loc (exhale_stmts @ [new_assign_stmt]) in
      
      Rewriter.return new_stmt
    )


  | _ -> Rewriter.Stmt.descend stmt ~f:rewrite_call_stmts


let rewrite_callable_pre_post_conds (c: Callable.t) : Callable.t Rewriter.t =
  let open Rewriter.Syntax in
  match c.call_def with
  | ProcDef proc ->
    (match proc.proc_body with
    | None -> Rewriter.return c
    | Some body ->
      let pre_conds = List.filter_map c.call_decl.call_decl_precond ~f:(fun spec ->
        if spec.spec_atomic then 
          None
        else
          Some (Stmt.mk_inhale_spec ~cmnt:(Some ("precond: " ^ Expr.to_string spec.spec_form)) ~loc:(Expr.to_loc spec.spec_form) spec))
      and post_conds = List.filter_map c.call_decl.call_decl_postcond ~f:(fun spec -> 
        if spec.spec_atomic then
          None
        else
          Some (Stmt.mk_exhale_spec ~cmnt:(Some ("postcond: " ^ Expr.to_string spec.spec_form)) ~loc:(Expr.to_loc spec.spec_form) spec))
      in

      let* pre_conds, post_conds = 
        if not (Callable.is_atomic c.call_decl) then
          Rewriter.return (pre_conds, post_conds)
        else
          let* callable_fully_qual_name = Rewriter.current_scope_id in

          let atomic_token_var = Expr.mk_var ~loc:(Stmt.loc body) ~typ:Type.atomic_token (QualIdent.from_ident (Rewriter.ProgUtils.callable_au_token_ident ~loc:(Stmt.loc body) c.call_decl.call_decl_name)) in

          let concrete_args = List.filter c.call_decl.call_decl_formals ~f:(fun var_decl -> not var_decl.var_implicit) in
          let concrete_args_expr = List.map concrete_args ~f:(Expr.from_var_decl) in

          let inhale_au = 
            Stmt.mk_inhale_expr ~cmnt:(Some "au_precond")~loc:(Stmt.loc body) (Expr.mk_app ~loc:(Stmt.loc body) ~typ:Type.perm (Expr.AUPred callable_fully_qual_name) (atomic_token_var :: concrete_args_expr)) in

          let exhale_au = 
            let ret_vars = List.map c.call_decl.call_decl_returns ~f:(fun var_decl -> Expr.from_var_decl var_decl) in
            let ret_expr = Expr.mk_tuple ~loc:(Stmt.loc body) ret_vars in
            
            Stmt.mk_exhale_expr ~cmnt:(Some "au_postcond") ~loc:(Stmt.loc body) (Expr.mk_app ~loc:(Stmt.loc body) ~typ:Type.perm (Expr.AUPredCommit callable_fully_qual_name) ((atomic_token_var :: concrete_args_expr) @ [ret_expr])) in
          
          Rewriter.return (inhale_au :: pre_conds, exhale_au :: post_conds)
      in

      let new_body = Stmt.mk_block_stmt ~loc:(Stmt.loc body) (pre_conds @ [body] @ post_conds) in
      let new_proc = Callable.{ call_decl = c.call_decl; call_def = ProcDef { proc_body = Some new_body } } in
      Rewriter.return new_proc
    )
  | FuncDef func ->
    Rewriter.return c

let rewrite_atomic_callable_token (c: Callable.t): Callable.t Rewriter.t = 
  let open Rewriter.Syntax in
  match c.call_def with
  | ProcDef proc ->
    (match proc.proc_body with
    | None -> Rewriter.return c
    | Some body ->
      if not (Callable.is_atomic c.call_decl) then
        Rewriter.return c
      else
        let atomic_token_var = 
          { Type.var_name = Rewriter.ProgUtils.callable_au_token_ident ~loc:(Stmt.loc body) c.call_decl.call_decl_name;
            var_loc = Stmt.loc body;
            var_type = Type.atomic_token;
            var_const = false;
            var_ghost = true;
            var_implicit = false;
          }
        in

        let* _ = Rewriter.introduce_symbol (Module.VarDef {var_decl = atomic_token_var; var_init = None}) in

        (* let* callable_fully_qual_name = Rewriter.current_scope_id in

        let inhale_au = 
          let concrete_args = List.filter c.call_decl.call_decl_formals ~f:(fun var_decl -> not var_decl.var_implicit) in
          let concrete_args_expr = List.map concrete_args ~f:(Expr.from_var_decl) in
          
          Stmt.mk_inhale_expr ~loc:(Stmt.loc body) (Expr.mk_app ~loc:(Stmt.loc body) ~typ:Type.perm (Expr.AUPred callable_fully_qual_name) (Expr.from_var_decl atomic_token_var :: concrete_args_expr)) in

        let new_body = Stmt.mk_block_stmt ~loc:(Stmt.loc body) [inhale_au; body] in *)
        (* let new_proc = Callable.{ c with call_def = ProcDef { proc_body = Some new_body } } in *)
        Rewriter.return c
    )
  | FuncDef func ->
    Rewriter.return c

let rec rewrite_frac_field_types (symbol: Module.symbol) : Module.symbol Rewriter.t =
  let open Rewriter.Syntax in
  match symbol with
  | ModDef _ | ModInst _ | TypeDef _ | ConstrDef _ | DestrDef _ |  VarDef _ | CallDef _ -> Rewriter.return symbol


  | FieldDef f ->
    let* is_field_an_ra = 
      begin
        match f.field_type with
        | App (Fld, [App (Var qual_iden, args, _)], _) ->
          assert (List.is_empty args);

          let module_name = QualIdent.pop qual_iden in

          let* does_module_implement_ra = 
            let* module_symbol = Rewriter.find_and_reify f.field_loc module_name in
            Rewriter.ProgUtils.does_symbol_implement_ra module_symbol
          in

          Rewriter.return does_module_implement_ra
        
        | _ -> Rewriter.return false

      end
    in

    Logs.debug (fun m -> m "Rewrites.rewrite_frac_field_types: is_field_an_ra: %s -> %b" (Type.to_string f.field_type) is_field_an_ra);
    if is_field_an_ra then
      Rewriter.return symbol
    else
      let field_underlying_tp = match f.field_type with
        | App (Fld, [tp_expr], _) -> tp_expr
        | _ -> Error.type_error f.field_loc "Expected field identifier."
      in 

      
      let* tp_module = Rewriter.ProgUtils.intros_type_module ~loc:(f.field_loc) ~f:Typing.process_symbol field_underlying_tp in

      let instantiated_frac_module = 
        Module.ModInst {
          mod_inst_name = Rewriter.ProgUtils.field_type_to_frac_mod_ident ~loc:f.field_loc f.field_type;
          mod_inst_type = Predefs.lib_cancellative_ra_mod_qual_ident;
          mod_inst_def = Some (Predefs.lib_frac_mod_qual_ident, [tp_module]);
          mod_inst_is_interface = false;
          mod_inst_loc = f.field_loc;
        } in
      
      (* let* topscope_name = Rewriter.ProgUtils.find_highest_valid_scope_type_expr f.field_loc field_underlying_tp in

      let topscope_name = match topscope_name with
        | Some topscope_name -> topscope_name
        | None -> Error.type_error f.field_loc ("Could not find a valid scope to add field " ^ (Ident.to_string f.field_name) ^ " to.")
      
      in *)


      let* frac_mod_name = Rewriter.introduce_typecheck_symbol ~loc:f.field_loc ~f:Typing.process_symbol instantiated_frac_module in

      let frac_type = Type.mk_fld f.field_loc (Type.mk_var f.field_loc (QualIdent.append frac_mod_name (Ident.make f.field_loc "T" 0))) in

      Rewriter.return (Module.FieldDef { f with field_type = frac_type })


let rec rewrite_own_expr_4_arg (expr: Expr.t) : Expr.t Rewriter.t =
  (* Rewrites expressions of the form `own(x, f, v, p)` to `own (x, f, Frac[f.type].frac_chunk(v, p)) 
     
  Essentially, makes a uniform 3-arg representation of all own expressions, frac-type as well as RA type.
  *)
  let open Rewriter.Syntax in

  Logs.debug (fun m -> m "Rewrites.rewrite_own_expr_4_arg: run on expr: %a" Expr.pr expr);


  match expr with
  | App (Own, expr1 :: expr2 :: expr3 :: expr4 :: [], expr_attr) ->
    Logs.debug (fun m -> m "Rewrites.rewrite_own_expr_4_arg: found expr: %a" Expr.pr expr);

    (* let field_type = match Expr.to_type expr2 with
      | App (Fld, [tp_expr], _) -> tp_expr
      | _ -> Error.type_error (Expr.to_loc expr2) "Expected field identifier."
    in *)

    let field_type = Expr.to_type expr2 in

    let+ expr3 =
      begin 
        let expr3_1 = expr3 in
        let expr3_2 = expr4 in

        Logs.debug (fun m -> m "Rewrites.rewrite_own_expr_4_arg: intros_type_module started: tp_module: %a" Type.pr field_type);

        let* frac_mod_name = Rewriter.resolve (Expr.to_loc expr) (QualIdent.from_ident (Rewriter.ProgUtils.field_type_to_frac_mod_ident ~loc:(Expr.to_loc expr) field_type)) in

        let frac_type = Type.mk_var (Expr.to_loc expr) (QualIdent.append frac_mod_name (Ident.make (Expr.to_loc expr) "T" 0)) in
        (* let frac_constr = Rewriter.find_and_reify (Expr.to_loc expr) (QualIdent.append frac_mod_name (Ident.make (Expr.to_loc expr) "frac_chunk" 0)) in *)
        let expr3 = Expr.mk_app ~loc:(Expr.to_loc expr) ~typ:frac_type (Expr.DataConstr (QualIdent.append frac_mod_name (Ident.make (Expr.to_loc expr) "frac_chunk" 0))) [expr3_1; expr3_2] in

        Rewriter.return expr3
      end 
    in

    Expr.App (Own, [expr1; expr2; expr3], expr_attr)

  | _ -> Rewriter.Expr.descend expr ~f:rewrite_own_expr_4_arg

let rec rewrite_new_stmt_heap_arg (stmt: Stmt.t) : Stmt.t Rewriter.t =
  let open Rewriter.Syntax in
  (* Logs.debug (fun m -> m "Rewrites.rewrite_new_stmt_heap_arg: stmt: %a" Stmt.pr stmt); *)

  match stmt.stmt_desc with
  | Basic (New new_desc) ->
    let* new_args = Rewriter.List.map new_desc.new_args ~f:(fun (field_name, expr_optn) ->
      match expr_optn with
      | None -> Rewriter.return (field_name, expr_optn)

      | Some expr ->
        let expr_typ = Expr.to_type expr in
        let* is_expr_typ_ra = Rewriter.ProgUtils.does_type_implement_ra expr_typ in

        Logs.debug (fun m -> m "Rewrites.rewrite_new_stmt_heap_arg: expr_typ_is_ra: %a -> %b" Type.pr expr_typ is_expr_typ_ra);

        if is_expr_typ_ra then
          Rewriter.return (field_name, expr_optn)
        else
          let* field_symbol = Rewriter.find_and_reify (Expr.to_loc expr) field_name in

          let* field_type = 
            match field_symbol with
            | FieldDef f -> Rewriter.return f.field_type
            | _ -> Error.error stmt.stmt_loc "Expected a field_def"
          in

          let frac_mod_name = match field_type with
          | App (Fld, [tp_expr], _) -> 
            (match tp_expr with
            | App (Var qual_iden, _, _) ->
              QualIdent.pop qual_iden
            | _ -> Error.type_error (Expr.to_loc expr) "Expected field identifier."
            )
          | _ -> Error.type_error (Expr.to_loc expr) "Expected field identifier."
          
          in

          Logs.debug (fun m -> m "Rewrites.rewrite_new_stmt_heap_arg: field_type: %a" Type.pr field_type);

          let frac_type = Type.mk_var (Expr.to_loc expr) (QualIdent.append frac_mod_name (Ident.make (Expr.to_loc expr) "T" 0)) in
          (* let frac_constr = Rewriter.find_and_reify (Expr.to_loc expr) (QualIdent.append frac_mod_name (Ident.make (Expr.to_loc expr) "frac_chunk" 0)) in *)
          let new_expr = Expr.mk_app ~loc:(Expr.to_loc expr) ~typ:frac_type (Expr.DataConstr (QualIdent.append frac_mod_name (Ident.make (Expr.to_loc expr) "frac_chunk" 0))) [expr; Expr.mk_real 1.0] in

          Rewriter.return (field_name, Some new_expr)
      
    )

    in

    Rewriter.return ({stmt with stmt_desc = (Basic (New { new_desc with new_args }))} )

  | _ -> Rewriter.Stmt.descend stmt ~f:rewrite_new_stmt_heap_arg

let rec expr_preds_mentioned (expr: Expr.t) : (QualIdent.t list) Rewriter.t =
  let open Rewriter.Syntax in 
  match expr with
  | App (Var qual_ident, _, _) ->
    let+ _, (_, symbol, _) = Rewriter.resolve_and_find (Expr.to_loc expr) qual_ident in

    (match symbol with
    | CallDef c -> 
      (match c.call_decl.call_decl_kind with
      | Pred | Invariant -> [qual_ident]
      | _ -> []
      )
    | _ -> []
    )
  | App (_, expr_list, _) ->
    Rewriter.List.fold_right expr_list ~init:([]) ~f:(fun expr acc ->
      let+ expr_predicates = expr_preds_mentioned expr in
      (acc @ expr_predicates)
    )

  | Binder (_, _, _, expr, _) ->
    expr_preds_mentioned expr

let stmt_preds_mentioned (s: Stmt.t) : (QualIdent.t list) Rewriter.t = 
  let open Rewriter.Syntax in
  let rec stmt_preds_mentioned (s: Stmt.t) : (QualIdent.t list) Rewriter.t =
    match s.stmt_desc with
    | Block b -> 
      let* block_preds = Rewriter.List.map b.block_body ~f:stmt_preds_mentioned in

      Rewriter.return (List.concat block_preds)
    
    | Loop l ->
      let* prebody_preds = stmt_preds_mentioned l.loop_prebody in
      (* let* test_preds = expr_preds_mentioned l.loop_test in *)
      let* postbody_preds = stmt_preds_mentioned l.loop_postbody in

      (* Rewriter.return (prebody_preds @ test_preds @ postbody_preds) *)
      Rewriter.return (prebody_preds @ postbody_preds)

    | Cond c ->
      (* let* test_preds = expr_preds_mentioned c.cond_test in *)
      let* then_preds = stmt_preds_mentioned c.cond_then in
      let* else_preds = stmt_preds_mentioned c.cond_else in

      (* Rewriter.return (test_preds @ then_preds @ else_preds) *)
      Rewriter.return (then_preds @ else_preds)

    | Basic s ->
      begin match s with
      | Spec (_, sp) -> 
        expr_preds_mentioned sp.spec_form
      
      | Use u ->
        Rewriter.return [u.use_name]
      
      | _ -> Rewriter.return []
      end

    in

  let* preds_list = stmt_preds_mentioned s in
  let preds_list = List.dedup_and_sort preds_list ~compare:QualIdent.compare in

  Rewriter.return preds_list


let rewrite_add_predicate_validity_lemmas (c: Callable.t) : Callable.t Rewriter.t =
  let open Rewriter.Syntax in

  match c.call_decl.call_decl_kind with
  | Pred | Invariant ->
    (match c.call_decl.call_decl_returns, c.call_def with
    | [], _ | _, FuncDef { func_body =  None} -> Rewriter.return c
    
    | rets, FuncDef { func_body =  Some body} ->
      let pred_valid_lemma_ident = Ident.fresh c.call_decl.call_decl_loc ("pred_valid$" ^ (Ident.to_string c.call_decl.call_decl_name)) in

      let formal_args, renaming_map1, renaming_map2, preconds =
        let renamings, in_args = List.fold_map c.call_decl.call_decl_formals ~init:(Map.empty (module QualIdent)) ~f:(fun acc_renamings var_decl ->
          let new_var_decl = { var_decl with var_name = Ident.fresh var_decl.var_loc var_decl.var_name.ident_name } in
          let new_var_expr = Expr.from_var_decl new_var_decl in

          (Map.add_exn acc_renamings ~key:(QualIdent.from_ident var_decl.var_name) ~data:new_var_expr), new_var_decl
        ) in

        let renamings1, out_args1 = List.fold_map rets ~init:renamings ~f:(fun acc_renamings var_decl ->
          let new_var_decl = { var_decl with var_name = Ident.fresh var_decl.var_loc var_decl.var_name.ident_name } in
          let new_var_expr = Expr.from_var_decl new_var_decl in

          (Map.add_exn acc_renamings ~key:(QualIdent.from_ident var_decl.var_name) ~data:new_var_expr), new_var_decl
        ) in

        let renamings2, out_args2 = List.fold_map rets ~init:renamings ~f:(fun acc_renamings var_decl ->
          let new_var_decl = { var_decl with var_name = Ident.fresh var_decl.var_loc var_decl.var_name.ident_name } in
          let new_var_expr = Expr.from_var_decl new_var_decl in

          (Map.add_exn acc_renamings ~key:(QualIdent.from_ident var_decl.var_name) ~data:new_var_expr), new_var_decl
        ) in

        let preconds = List.map2_exn out_args1 out_args2 ~f:(fun out_arg1 out_arg2 ->
          let spec_expr = Expr.mk_not (Expr.mk_eq ~loc:(Expr.to_loc body) (Expr.from_var_decl out_arg1) (Expr.from_var_decl out_arg2)) in
          
          Stmt.mk_spec spec_expr
        ) in

        in_args @ out_args1 @ out_args2, renamings1, renamings2, preconds
      in

      let postcond = 
        Stmt.mk_spec (Expr.mk_bool ~loc:(Expr.to_loc body) false)
      in

      let call_decl = {
        Callable.call_decl_kind = Lemma;
        call_decl_name = pred_valid_lemma_ident;
        call_decl_formals = formal_args;
        call_decl_returns = [];
        call_decl_locals = [];
        call_decl_precond = preconds;
        call_decl_postcond = [postcond];
        call_decl_is_free = false;
        call_decl_is_auto = false;
        call_decl_loc = c.call_decl.call_decl_loc;
      }

      in

      let call_body = Stmt.mk_block_stmt ~loc:c.call_decl.call_decl_loc [
        Stmt.mk_inhale_expr ~loc:c.call_decl.call_decl_loc (Expr.alpha_renaming body renaming_map1);
        Stmt.mk_inhale_expr ~loc:c.call_decl.call_decl_loc (Expr.alpha_renaming body renaming_map2);
      ] in

      let call_def = Module.CallDef (Callable.{ call_decl; call_def = ProcDef { proc_body = Some call_body } }) in

      let* _ = Rewriter.introduce_typecheck_symbol ~loc:c.call_decl.call_decl_loc ~f:Typing.process_symbol call_def in

      Rewriter.return c

    | _, ProcDef _ -> Error.internal_error c.call_decl.call_decl_loc "Expected a function definition for a predicate"
    )

  | _ -> Rewriter.return c




module AtomicityAnalysis = struct
  type au_token = { 
    token: QualIdent.t; 
    callable: QualIdent.t; 
    callable_args: expr list; 
    implicit_bound_vars: expr list; 
  }

  type invs = {
    inv_name: QualIdent.t;
    inv_args: Expr.t list;
  }

  type atomicity_check = {
    au_opened: au_token list;
    invs_opened: invs list;
    atomic_step_taken: bool;
  }

  let take_atomic_step ~loc (state: atomicity_check) : atomicity_check =
    if (List.is_empty state.au_opened) && (List.is_empty state.invs_opened) then
      state
    else
      match state.atomic_step_taken with
      | false -> { state with atomic_step_taken = true }
      | true -> Error.error loc "Multiple atomic steps taken in a single atomic block"

  let take_non_atomic_step ~loc (state: atomicity_check) : atomicity_check =
    if (List.is_empty state.au_opened) && (List.is_empty state.invs_opened) then
      state
    else
      Error.error loc "Cannot take a non-atomic step inside an atomic block"

  let open_inv ~loc (inv_name, inv_args) atomicity_state : atomicity_check =
    if List.exists atomicity_state.invs_opened ~f:(fun inv -> QualIdent.(inv.inv_name = inv_name) && List.for_all2_exn inv_args inv.inv_args ~f:(Expr.alpha_equal)) then
      Error.error loc "Invariant already opened"
    else
    { atomicity_state with invs_opened = { inv_name; inv_args} :: atomicity_state.invs_opened }

  let close_inv ~loc (inv_name, inv_args) atomicity_state : atomicity_check =
    if not (List.exists atomicity_state.invs_opened ~f:(fun inv -> QualIdent.(inv.inv_name = inv_name) && List.for_all2_exn inv_args inv.inv_args ~f:(Expr.alpha_equal))) then
      Error.error loc "Invariant not already opened"
    else
    let invs_opened = List.filter atomicity_state.invs_opened ~f:(fun inv -> not (QualIdent.(inv.inv_name = inv_name) && List.for_all2_exn inv_args inv.inv_args ~f:(Expr.alpha_equal))) in

    if List.is_empty invs_opened && List.is_empty atomicity_state.au_opened then
      { atomicity_state with invs_opened; atomic_step_taken = false }
    else
      { atomicity_state with invs_opened }

  let open_au ~loc (token, callable, callable_args, implicit_bound_vars) atomicity_state : atomicity_check =
    if List.exists atomicity_state.au_opened ~f:(fun au -> QualIdent.(au.token = token)) then
      Error.error loc "Atomic token already opened"
    else
    { atomicity_state with au_opened = { token; callable; callable_args; implicit_bound_vars } :: atomicity_state.au_opened }

  let close_au ~loc token atomicity_state : atomicity_check =
    if not (List.exists atomicity_state.au_opened ~f:(fun au -> QualIdent.(au.token = token))) then
      Error.error loc "Atomic token not already opened"
    else
    let au_opened = List.filter atomicity_state.au_opened ~f:(fun au -> not (QualIdent.(au.token = token))) in

    if List.is_empty au_opened && List.is_empty atomicity_state.invs_opened then
      { atomicity_state with au_opened; atomic_step_taken = false }
    else
      { atomicity_state with au_opened }

  let rec is_expr_atomic (expr: Expr.t) : bool =
    match expr with
    | App (constr, expr_args, _) ->
      (match constr with
      | Null | Int _ | Real _ | Bool _ -> true
      | Var _ ->
        (match expr_args with
        | [] -> true
        | _ -> false
        )
      | Read -> is_expr_atomic (List.hd_exn expr_args)
      | _ -> false)

    | _ -> false
  

  let rewrite_au_cmnds ~(ghost_block: bool) (stmt: Stmt.t) : (Stmt.t, atomicity_check) Rewriter.t_ext =
    let open Rewriter.Syntax in

    let rec rewrite_au_cmnds ~(ghost_block: bool) (stmt: Stmt.t) : (Stmt.t, atomicity_check) Rewriter.t_ext =  
      let* curr_callable_name = Rewriter.current_scope_id in
      let* curr_callable = 
        let* symbol = Rewriter.find_and_reify stmt.stmt_loc curr_callable_name in
        (match symbol with
        | CallDef c -> Rewriter.return c
        | _ -> Error.error stmt.stmt_loc "Expected a call_def"
        )
      in

      let concrete_args = List.filter curr_callable.call_decl.call_decl_formals ~f:(fun var_decl -> not var_decl.var_implicit) in
      let implicit_args = List.filter curr_callable.call_decl.call_decl_formals ~f:(fun var_decl -> var_decl.var_implicit) in

      Logs.debug (fun m -> m "Rewrites.rewrite_au_cmnds: curr_callable_name: %a" QualIdent.pr curr_callable_name);

      let loc = stmt.stmt_loc in

      let* atomicity_state = Rewriter.current_user_state in

      match stmt.stmt_desc with
      | Basic (New new_desc) ->
        let* new_lhs = 
          let* symbol = Rewriter.find_and_reify stmt.stmt_loc new_desc.new_lhs in
          (match symbol with
          | VarDef v -> Rewriter.return v
          | _ -> Error.error stmt.stmt_loc "Expected a var_def"
          )
        in

        if new_lhs.var_decl.var_ghost then
          Rewriter.return stmt
        else
          (if ghost_block then
            Error.error stmt.stmt_loc "Cannot allocate non-ghost variables in a ghost block"
          else
            let atomicity_state = take_atomic_step ~loc atomicity_state in
          let* _ = Rewriter.set_user_state atomicity_state in
          Rewriter.return stmt)
        
      | Basic (Assign assign_desc) ->
        let* is_assign_desc_lhs_ghost = (Rewriter.List.for_all assign_desc.assign_lhs ~f:(fun expr ->
          match expr with
          | App (Var qual_iden, [], _) ->
            let* symbol = Rewriter.find_and_reify stmt.stmt_loc qual_iden in
            (match symbol with
            | VarDef v -> Rewriter.return v.var_decl.var_ghost
            | _ -> Error.error stmt.stmt_loc "Expected a var_def"
            )
          
          | App (Read, [loc_expr; field_expr], _) ->
            Rewriter.return false

          | _ -> Error.error stmt.stmt_loc "Expected a variable"
        ))

        in

        if is_assign_desc_lhs_ghost then
          Rewriter.return stmt
        (* else if ghost_block then
          Error.error stmt.stmt_loc "Cannot assign to non-ghost variables in a ghost block" *)
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
        let* is_bind_lhs_ghost = (Rewriter.List.for_all bind_desc.bind_lhs ~f:(fun expr ->
          match expr with
          | App (Var qual_iden, [], _) ->
            let* symbol = Rewriter.find_and_reify stmt.stmt_loc qual_iden in
            (match symbol with
            | VarDef v -> Rewriter.return v.var_decl.var_ghost
            | _ -> Error.error stmt.stmt_loc "Expected a var_def"
            )

          | _ -> Error.error stmt.stmt_loc "Expected a variable"
        ))
        in

        if is_bind_lhs_ghost then
          Rewriter.return stmt
        else
          Error.error stmt.stmt_loc "Cannot bind non-ghost variables"

      | Basic (FieldRead field_read_desc) ->
        let* symbol = Rewriter.find_and_reify stmt.stmt_loc field_read_desc.field_read_lhs in
        (match symbol with
        | VarDef v -> 
          if v.var_decl.var_ghost then
            Rewriter.return stmt
          else
            let atomicity_state = take_atomic_step ~loc atomicity_state in
            let* _ = Rewriter.set_user_state atomicity_state in
            Rewriter.return stmt
        | _ -> Error.error stmt.stmt_loc "Expected a var_def"
        )
        
      | Basic (Havoc qual_iden) ->
        let* symbol = Rewriter.find_and_reify stmt.stmt_loc qual_iden in
        (match symbol with
        | VarDef v -> 
          if v.var_decl.var_ghost then
            Rewriter.return stmt
          else if ghost_block then
            Error.error stmt.stmt_loc "Cannot havoc non-ghost variables in a ghost block"
          else
            let atomicity_state = take_atomic_step ~loc atomicity_state in
            let* _ = Rewriter.set_user_state atomicity_state in
            Rewriter.return stmt
        | _ -> Error.error stmt.stmt_loc "Expected a var_def"
        )

      | Basic (Call call_desc) ->
        let* symbol = Rewriter.find_and_reify stmt.stmt_loc call_desc.call_name in
        let call_decl, call_def = (match symbol with
          | CallDef c -> c.call_decl, c.call_def
          | _ -> Error.error stmt.stmt_loc "Expected a call_def"
        ) in

        let* is_call_lhs_ghost = (Rewriter.List.for_all call_desc.call_lhs ~f:(fun qual_iden ->
          let* symbol = Rewriter.find_and_reify stmt.stmt_loc qual_iden in
          (match symbol with
          | VarDef v -> Rewriter.return v.var_decl.var_ghost
          | _ -> Error.error stmt.stmt_loc "Expected a var_def"
          )
        ))
        in

        if is_call_lhs_ghost then
          Rewriter.return stmt
        else if ghost_block then
          Error.error stmt.stmt_loc "Cannot assign to non-ghost variables in a ghost block"
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
        else
        if is_expr_atomic return_expr then
          let atomicity_state = take_atomic_step ~loc atomicity_state in
          let* _ = Rewriter.set_user_state atomicity_state in
          Rewriter.return stmt
        else
          let atomicity_state = take_non_atomic_step ~loc atomicity_state in
          let* _ = Rewriter.set_user_state atomicity_state in
          Rewriter.return stmt

      | Basic (Use use_desc) ->
        let* symbol = Rewriter.find_and_reify stmt.stmt_loc use_desc.use_name in
        (match symbol with
        | CallDef c -> 
          (match c.call_decl.call_decl_kind with
          | Pred ->
            Rewriter.return stmt
          | Invariant ->
            
            let atomicity_state = 
              (match use_desc.use_kind with
              | Unfold -> open_inv ~loc (use_desc.use_name, use_desc.use_args) atomicity_state 
              | Fold -> close_inv ~loc (use_desc.use_name, use_desc.use_args) atomicity_state
              | OpenInv | CloseInv -> Error.internal_error stmt.stmt_loc "Unsupported"
              )
              
            in
            let* _ = Rewriter.set_user_state atomicity_state in
            Rewriter.return stmt
          | _ -> Error.error stmt.stmt_loc "Expected a pred or invariant")
        | _ -> Error.error stmt.stmt_loc "Expected a call_def")    

      | Basic (AUAction auaction_desc) ->
        (match auaction_desc.auaction_kind with
        | BindAU qual_iden ->
          let* qual_iden_var =
            let+ symbol = Rewriter.find_and_reify stmt.stmt_loc qual_iden in
            (match symbol with
            | VarDef v ->
              v
            | _ -> Error.error stmt.stmt_loc "Expected a var_def"
            )
          in

          let* au_token_var = 
            let+ symbol = Rewriter.find_and_reify stmt.stmt_loc (QualIdent.from_ident (Rewriter.ProgUtils.callable_au_token_ident ~loc:(Stmt.loc stmt) (QualIdent.unqualify curr_callable_name))) in
            (match symbol with
            | VarDef v ->
              v 
            | _ -> Error.error stmt.stmt_loc "Expected a var_def"
            )
          in

          let assign_stmt = Stmt.mk_assign ~loc:(Stmt.loc stmt) [Expr.from_var_decl qual_iden_var.var_decl] (Expr.from_var_decl au_token_var.var_decl) in

          Rewriter.return assign_stmt

        | OpenAU (token, callable, bound_vars) -> 
          let exhale_stmt = Stmt.mk_exhale_expr ~cmnt:(Some ("OpenAU: " ^ Stmt.to_string stmt)) ~loc:(Stmt.loc stmt) (Expr.mk_app ~loc:(Stmt.loc stmt) ~typ:Type.perm (AUPred curr_callable_name) (Expr.mk_var ~typ:Type.atomic_token token :: (List.map concrete_args ~f:(Expr.from_var_decl)))) in

          (match callable with
          | Some _ -> Error.error stmt.stmt_loc "Unsupported to open another callable"
          | None ->
            let alpha_renaming_map = List.fold2_exn implicit_args bound_vars ~init:(Map.empty (module QualIdent)) ~f:(fun acc_map implicit_arg bound_var ->
              Map.add_exn acc_map ~key:(QualIdent.from_ident implicit_arg.var_name) ~data:bound_var
            ) in

            let inhale_stmts = List.filter_map curr_callable.call_decl.call_decl_precond ~f:(fun spec ->
              if not spec.spec_atomic then 
                None
              else
                Some (Stmt.mk_inhale_expr ~cmnt:(Some ("OpenAU: " ^ Stmt.to_string stmt)) ~loc:(Stmt.loc stmt) (Expr.alpha_renaming spec.spec_form alpha_renaming_map))
            ) in

            let atomicity_state = open_au ~loc (token, curr_callable_name, (List.map concrete_args ~f:(Expr.from_var_decl)), bound_vars) atomicity_state in
            let* _ = Rewriter.set_user_state atomicity_state in

            let new_stmt = Stmt.mk_block_stmt ~loc:(Stmt.loc stmt) (exhale_stmt :: inhale_stmts) in

            Rewriter.return new_stmt
          
          )
        | AbortAU token | CommitAU (token, _) ->
          let opened_au_token = List.find atomicity_state.au_opened ~f:(fun au_token -> QualIdent.equal au_token.token token) in

          let opened_au_token = (match opened_au_token with
          | None ->
            Error.error stmt.stmt_loc "No opened AU token found to abort"
          | Some opened_au_token -> opened_au_token
          ) in

          let* callable_decl = 
            let+ symbol = Rewriter.find_and_reify stmt.stmt_loc opened_au_token.callable in
            (match symbol with
            | CallDef c -> c.call_decl
            | _ -> Error.error stmt.stmt_loc "Expected a call_def"
            )
          in

          let alpha_renaming_map = List.fold2_exn callable_decl.call_decl_formals (opened_au_token.callable_args @ opened_au_token.implicit_bound_vars) ~init:(Map.empty (module QualIdent)) ~f:(fun acc_map formal_arg actual_arg ->
            Map.add_exn acc_map ~key:(QualIdent.from_ident formal_arg.var_name) ~data:actual_arg
          ) in

          let exhale_stmts, inhale_stmt, atomicity_state = (match auaction_desc.auaction_kind with
          | AbortAU token ->
            let exhale_stmts = List.filter_map callable_decl.call_decl_precond ~f:(fun spec ->
              if not spec.spec_atomic then 
                None
              else
                Some (Stmt.mk_exhale_expr ~cmnt:(Some ("AbortAU: " ^ Stmt.to_string stmt)) ~loc:(Stmt.loc stmt) (Expr.alpha_renaming spec.spec_form alpha_renaming_map))
            ) in

            let inhale_stmt = Stmt.mk_inhale_expr ~cmnt:(Some ("AbortAU: " ^ Stmt.to_string stmt)) ~loc:(Stmt.loc stmt) (Expr.mk_app ~loc:(Stmt.loc stmt) ~typ:Type.perm (AUPred opened_au_token.callable) (Expr.mk_var ~typ:Type.atomic_token opened_au_token.token :: (opened_au_token.callable_args))) in

            let atomicity_state = close_au ~loc token atomicity_state in

            exhale_stmts, inhale_stmt, atomicity_state

          | CommitAU (token, ret_exprs) ->
            let alpha_renaming_map = List.fold2_exn callable_decl.call_decl_returns ret_exprs ~init:alpha_renaming_map ~f:(fun acc_map formal_arg actual_arg ->
              Map.add_exn acc_map ~key:(QualIdent.from_ident formal_arg.var_name) ~data:actual_arg
            ) in

            let exhale_stmts = List.filter_map callable_decl.call_decl_postcond ~f:(fun spec ->
              if not spec.spec_atomic then 
                None
              else
                Some (Stmt.mk_exhale_expr ~cmnt:(Some ("CommitAU: " ^ Stmt.to_string stmt)) ~loc:(Stmt.loc stmt) (Expr.alpha_renaming spec.spec_form alpha_renaming_map))
            ) in

            let inhale_stmt = Stmt.mk_inhale_expr ~cmnt:(Some ("CommitAU: " ^ Stmt.to_string stmt)) ~loc:(Stmt.loc stmt) (Expr.mk_app ~loc:(Stmt.loc stmt) ~typ:Type.perm (AUPredCommit opened_au_token.callable) (Expr.mk_var ~typ:Type.atomic_token opened_au_token.token :: opened_au_token.callable_args @ [(Expr.mk_tuple ret_exprs)])) in

            let atomicity_state = close_au ~loc token atomicity_state in

            exhale_stmts, inhale_stmt, atomicity_state

          | _ -> assert false
          ) in

          let new_stmt = Stmt.mk_block_stmt ~loc:(Stmt.loc stmt) (exhale_stmts @ [inhale_stmt]) in

          let* _ = Rewriter.set_user_state atomicity_state in

          Rewriter.return new_stmt
        )

      | Block block_desc when block_desc.block_is_ghost -> 
                Rewriter.Stmt.descend stmt ~f:(rewrite_au_cmnds ~ghost_block:true) 

      | Block block_desc ->
                Rewriter.Stmt.descend stmt ~f:(rewrite_au_cmnds ~ghost_block) 
      
      | Cond cond_desc ->
        let* then_stmt = Rewriter.Stmt.descend cond_desc.cond_then ~f:(rewrite_au_cmnds ~ghost_block) in
        let* then_atomicity_state = Rewriter.current_user_state in

        let* _ = Rewriter.set_user_state atomicity_state in
        let* else_stmt = Rewriter.Stmt.descend cond_desc.cond_else ~f:(rewrite_au_cmnds ~ghost_block) in
        let* else_atomicity_state = Rewriter.current_user_state in

        let if_else_atomicity_states_equal = 
          if (List.length then_atomicity_state.invs_opened = List.length else_atomicity_state.invs_opened) && (List.length then_atomicity_state.au_opened = List.length else_atomicity_state.au_opened) then
            List.for_all2_exn then_atomicity_state.invs_opened else_atomicity_state.invs_opened ~f:(fun inv1 inv2 -> QualIdent.equal inv1.inv_name inv2.inv_name && List.for_all2_exn inv1.inv_args inv2.inv_args ~f:(Expr.alpha_equal))
            && List.for_all2_exn then_atomicity_state.au_opened else_atomicity_state.au_opened ~f:(fun au1 au2 -> QualIdent.equal au1.token au2.token && QualIdent.equal au1.callable au2.callable && List.for_all2_exn au1.callable_args au2.callable_args ~f:(Expr.alpha_equal) && List.for_all2_exn au1.implicit_bound_vars au2.implicit_bound_vars ~f:(Expr.alpha_equal))
            (* && Bool.(then_atomicity_state.atomic_step_taken = else_atomicity_state.atomic_step_taken) *)
          else
            false

        in

        if if_else_atomicity_states_equal then
          let new_stmt = {stmt with stmt_desc = (Cond { cond_desc with cond_then = then_stmt; cond_else = else_stmt }) } in

          if ghost_block then
            Rewriter.return new_stmt
          else 
            let atomicity_state = take_non_atomic_step ~loc else_atomicity_state in
            let* _ = Rewriter.set_user_state atomicity_state in
            Rewriter.return new_stmt
        else
          Error.error stmt.stmt_loc "Inconsistent atomicity states in then and else branches"

      | _ ->
        Rewriter.Stmt.descend stmt ~f:(rewrite_au_cmnds ~ghost_block)

    in

    let* stmt = rewrite_au_cmnds ~ghost_block stmt in
    let* atomicity_state = Rewriter.current_user_state in

    if List.is_empty atomicity_state.au_opened && List.is_empty atomicity_state.invs_opened then
      Rewriter.return stmt
    else
      Error.error stmt.stmt_loc "Unclosed AU token or invariant"

end

module HeapsExplicitTrnsl = struct
  (**
  
  The following grammar of assertion expressions is supported:

        a :=
            e ==> a
            e ? a : a 
            a && a
            a2

        a2 :=
            a2 && a2
            a2'
            forall (x:T)* :: a2

        a2' := 
            a2' && a2'
            e ==> a2'
            e ? a2' : a2'
            a1

        a1 :=
            a1'
            a1 && a1
            exists (x:T)* :: a1

        a1' :=
            a1' && a1'
            e ==> a1'
            e ? a1' : a1'
            a0

        a0 :=
            a0 && a0
            own(e, f, v)
            pred_name( e* )
            e
  *)
  
  type inhale_exhale = Inhale | Exhale
  type conditionals = (Expr.t list * Expr.t list)
  type conditions = Expr.t list
  (* Two componends in conditionals are used to keep track of conditionals given before existential quants, and ones given after existential quants *)

  type universal_quants = {
    univ_vars: (ident * var_decl) list;
    triggers: expr list list;
  }

  type existential_quant_record = { 
    var_decl: var_decl;
    quantified_exprs: (expr * conditionals) list;
  }

  type existential_quants = existential_quant_record IdentMap.t

  let unsupported_expr_error (expr: Expr.t) : 'a =
    Error.error (Expr.to_loc expr) ("Unsupported expression under inhale/exhale: " ^ (Expr.to_string expr))

  let field_heap_name (field_name: qual_ident) = 
    let field_name_str = QualIdent.to_string field_name in
    let field_name_str = Rewriter.ProgUtils.serialize field_name_str in
    Ident.make (Loc.dummy) (field_name_str ^ "$Heap") 0

  let field_heap_name2 (field_name: qual_ident) = 
    let field_name_str = QualIdent.to_string field_name in
    let field_name_str = Rewriter.ProgUtils.serialize field_name_str in
    Ident.make (Loc.dummy) (field_name_str ^ "$Heap2") 0

  let pred_heap_name (pred_name: qual_ident) = 
    let pred_name_str = QualIdent.to_string pred_name in
    let pred_name_str = Rewriter.ProgUtils.serialize pred_name_str in
    Ident.make (Loc.dummy) (pred_name_str ^ "$Heap") 0

  let pred_heap_name2 (pred_name: qual_ident) = 
    let pred_name_str = QualIdent.to_string pred_name in
    let pred_name_str = Rewriter.ProgUtils.serialize pred_name_str in
    Ident.make (Loc.dummy) (pred_name_str ^ "$Heap2") 0

  let au_heap_name (callable_name: qual_ident) = 
    let callable_name_str = QualIdent.to_string callable_name in
    let callable_name_str = Rewriter.ProgUtils.serialize callable_name_str in
    Ident.make (Loc.dummy) (callable_name_str ^ "$AU_Heap") 0

  let au_heap_name2 (callable_name: qual_ident) = 
    let callable_name_str = QualIdent.to_string callable_name in
    let callable_name_str = Rewriter.ProgUtils.serialize callable_name_str in
    Ident.make (Loc.dummy) (callable_name_str ^ "$AU_Heap2") 0


  let generate_inv_function (universal_quants: universal_quants) ((conds1, conds2): conditionals) (existential_quants: existential_quants) (expr: expr) (var: ident): qual_ident Rewriter.t =
    let open Rewriter.Syntax in

    let inv_fn_ident = Ident.fresh (Expr.to_loc expr) ("$inv_" ^ (Ident.to_string var)) in


    let arg_ident = Ident.fresh (Expr.to_loc expr) "res" in
    let arg_type = Expr.to_type expr in
    let formal_var_decls = [
      { 
        Type.var_name = arg_ident; 
        var_loc = Expr.to_loc expr; 
        var_type = arg_type; 
        var_const = true; 
        var_ghost = false; 
        var_implicit = false; }
    ] in

    let ret_type =
      let exist_var = match Map.find existential_quants var with
        | Some { var_decl; _ } -> var_decl
        | None -> Error.error (Loc.dummy) "Expected to find existential quant record" in
      exist_var.var_type

    in
    let ret_var_decl = {
      Type.var_name = Ident.fresh (Expr.to_loc expr) ("ret_" ^ (Ident.to_string var));
      var_loc = Expr.to_loc expr;
      var_type = ret_type;
      var_const = true;
      var_ghost = false;
      var_implicit = false;
    } in

    (*       ensures forall a, b, c, d, e, f :: m1(a,b,c) && m2(a, b, c, d, e, f) && v == f2(a, b, c, d, e, f) ==> d == ret *)
    let postcond =
      let spec_form = 
        let var_decls_forall = (List.map universal_quants.univ_vars ~f:(fun (var, var_decl) -> var_decl)) in
        let var_decls_existentials = (List.map (Map.to_alist existential_quants) ~f:(fun (var, { var_decl; _ }) -> var_decl)) in
        let var_decls = var_decls_forall @ var_decls_existentials in


        let eq_expr = Expr.mk_eq
          (Expr.mk_var ~typ:arg_type (QualIdent.from_ident arg_ident))    
          expr
        in

        Expr.mk_binder ~loc:(Expr.to_loc expr) ~typ:Type.bool Forall var_decls (
          Expr.mk_app ~loc:(Expr.to_loc expr) ~typ:Type.bool Expr.Impl [
            Expr.mk_and ~loc:(Expr.to_loc expr) ( eq_expr :: conds1 @ conds2);

            Expr.mk_eq ~loc:(Expr.to_loc expr) 
              (Expr.mk_var ~typ:ret_type (QualIdent.from_ident ret_var_decl.var_name)) 
              (Expr.mk_var ~typ:ret_type (QualIdent.from_ident var))
          ]
        )

    in
      
    Stmt.mk_spec spec_form

    in

    let call_decl = {
      Callable.call_decl_kind = Func;
      call_decl_name = inv_fn_ident;
      call_decl_formals = formal_var_decls;
      call_decl_returns = [ret_var_decl];
      call_decl_locals = [];
      call_decl_precond = [];
      call_decl_postcond = [postcond];
      call_decl_is_free = false;
      call_decl_is_auto = false;
      call_decl_loc = Expr.to_loc expr;
    }
      
    in

    let* inv_fn_qual_ident = 
      let+ module_qual_ident = Rewriter.current_module_name in

      QualIdent.append module_qual_ident inv_fn_ident

    in

    let fn_def = Module.CallDef (Callable.{ call_decl; call_def = FuncDef { func_body = None;} }) in
    

    let+ _ = Rewriter.introduce_symbol fn_def in
    
    inv_fn_qual_ident



  

  let generate_injectivity_assertions (universal_quants: universal_quants) (conditions: conditions) (expr: expr) : Stmt.t Rewriter.t =
    (* Running example : 
        Say we have:
        forall a, b :: p1(a, b) && p2(a, b) ==> f(a, b) 

        universal_quants : { a, b }
        conditions : [ p1(a, b); p2(a, b) ]
        expr : f(a, b)

    
    *)

    let univ_quants_list = universal_quants.univ_vars in
  
    (* [a, b] *)
    let univ_vars = List.map univ_quants_list ~f:(fun (_, var_decl) -> var_decl) in

    (* [a', b'] *)
    let dup_vars = List.map univ_quants_list ~f:(fun (_, var_decl) -> {var_decl with 
      var_name = Ident.fresh (Expr.to_loc expr) var_decl.var_name.ident_name}) in
    
    let alpha_renaming_map = List.fold2_exn univ_vars dup_vars ~init:(Map.empty (module QualIdent)) ~f:(fun map old_var_decl new_var_decl ->
      Map.add_exn map ~key:(QualIdent.from_ident old_var_decl.var_name) ~data:(Expr.mk_var ~typ:new_var_decl.var_type (QualIdent.from_ident new_var_decl.var_name))
    ) in

    (* [p1(a', b'); p2(a', b')] *)
    let renamed_conditions = 
      List.map conditions ~f:(fun cond -> Expr.alpha_renaming cond alpha_renaming_map) in

    (* f(a, b) == f(a', b') *)
    let expr_eq = Expr.mk_eq expr (Expr.alpha_renaming expr alpha_renaming_map) in

    (* [a == a'; b == b']  *)
    let vars_eq_list = List.map2_exn univ_vars dup_vars ~f:(fun old_var_decl new_var_decl -> 
      Expr.mk_eq (Expr.mk_var ~typ:old_var_decl.var_type (QualIdent.from_ident old_var_decl.var_name)) (Expr.mk_var ~typ:new_var_decl.var_type (QualIdent.from_ident new_var_decl.var_name))
    ) in

    let assert_expr = 
      (* forall a, b, a', b' :: 
         f(a, b) == f(a', b') && p1(a, b) && p2(a, b) && p1(a', b') && p2(a', b')  ==>
          a == a' && b == b'
         *)
    Expr.mk_binder ~loc:(Expr.to_loc expr) ~typ:Type.bool Forall (univ_vars @ dup_vars)
      (Expr.mk_impl 
        (Expr.mk_and (expr_eq :: conditions @ renamed_conditions ))

        (Expr.mk_and vars_eq_list))

    in

    let assert_stmt = Stmt.mk_assert_expr ~loc:(Expr.to_loc expr) assert_expr

    in
      
    Rewriter.return assert_stmt


  let generate_skolem_function (universal_quants: universal_quants) (var_decl: var_decl) ?(postconds: expr list = []) ?(optn_args: (var_decl * expr) list = []) ~loc : expr Rewriter.t = 
    let open Rewriter.Syntax in
    let univ_quants_list = universal_quants.univ_vars in

    let skolem_fn_ident = Ident.fresh loc ("$skolem_" ^ (Ident.to_string var_decl.var_name)) in

    let formal_var_decls = 
      List.map univ_quants_list ~f:(fun (v, v_decl) -> 
        { 
          Type.var_name = v_decl.var_name; 
          var_loc = loc; 
          var_type = v_decl.var_type; 
          var_const = true; 
          var_ghost = false; 
          var_implicit = false; 
        }
      ) @

      List.map optn_args ~f:(fun (v_decl, _) -> 
        { 
          Type.var_name = v_decl.var_name; 
          var_loc = loc; 
          var_type = v_decl.var_type; 
          var_const = true; 
          var_ghost = false; 
          var_implicit = false; 
        }
      )

    in

    let ret_var_decl = {
      Type.var_name = Ident.fresh loc ("ret_" ^ (Ident.to_string var_decl.var_name));
      var_loc = loc;
      var_type = var_decl.var_type;
      var_const = true;
      var_ghost = false;
      var_implicit = false;
    } in

    let postconds = List.map postconds ~f:(fun postcond -> 
      Expr.alpha_renaming postcond (Map.singleton (module QualIdent) (QualIdent.from_ident var_decl.var_name) (Expr.from_var_decl ret_var_decl))
      
    ) in

    let postconds = List.map postconds ~f:(fun postcond -> 
      Stmt.mk_spec postcond
    ) in

    let call_decl = {
      Callable.call_decl_kind = Func;
      call_decl_name = skolem_fn_ident;
      call_decl_formals = formal_var_decls;
      call_decl_returns = [ret_var_decl];
      call_decl_locals = [];
      call_decl_precond = [];
      call_decl_postcond = postconds;
      call_decl_loc = loc;
      call_decl_is_free = false;
      call_decl_is_auto = false;
    }

    in

    let* skolem_fn_qual_ident = 
      let+ module_qual_ident = Rewriter.current_module_name in

      QualIdent.append module_qual_ident skolem_fn_ident

    in
  
    let callable = Callable.{ call_decl; call_def = FuncDef { func_body = None;} }

    
    in

    let symbol = Module.CallDef callable in

    let* _ = Rewriter.introduce_typecheck_symbol ~loc ~f:(Typing.process_symbol) symbol in

    let ret_expr_args_list = (List.map univ_quants_list ~f:(fun (_, vd) -> Expr.from_var_decl vd)) @ (List.map optn_args ~f:(fun (_, expr) -> expr)) in

    let ret_expr = Expr.mk_app ~typ:var_decl.var_type (Expr.Var skolem_fn_qual_ident) ret_expr_args_list in

    Rewriter.return ret_expr


  let generate_utils_module ~(is_field:bool) (mod_ident: ident) (ra_qual_ident: qual_ident) ?(in_arg_typ = Type.ref) (loc: location): Module.symbol Rewriter.t =
    assert (not (is_field) || (is_field && (Type.equal in_arg_typ Type.ref)));

    let open Rewriter.Syntax in

           (* 
        module f$utils {
          type T = f.field_type.T;

          var id : T = f.field_type.id;

          func f$heapValid(h: Map[Ref, T]) returns (ret:Bool) {
            forall l: Ref :: T.valid(h[l])
          }

          func f$heapChunkComp(x1: T, x2: T) returns (ret: T) {
            T.comp(x1, x2)
          }

          func f$heapChunkFrame(x1: T, x2: T) returns (ret: T) {
            T.frame(x1, x2)
          }

          func f$heapchunk_compare(x1: T, x2: T) returns (ret: Bool) {
            T.valid(f$heapSubChunk(x1, x2))
          }
        }
        *)

        (* let fld_elem_type = match f.field_type with
          | App (Fld, [tp_expr], _) -> tp_expr
          | _ -> Error.type_error f.field_loc "Expected field identifier." 
        
        in *)

        let fld_elem_type = Rewriter.ProgUtils.get_ra_rep_type ra_qual_ident in

        let mod_decl = {
          Module.mod_decl_name = mod_ident;
          mod_decl_formals = [];
          mod_decl_returns = None;
          mod_decl_interfaces = Set.empty (module QualIdent);
          mod_decl_rep = None;
          mod_decl_is_ra = false;
          mod_decl_is_interface = false;
          mod_decl_loc = loc;
        } 
          
        in

        let* mod_def =
          let type_ident = Rewriter.ProgUtils.heap_utils_rep_type_ident loc in
          let type_tp_expr = Type.mk_var loc (QualIdent.from_ident type_ident) in

          let type_def = {
            Module.type_def_name = type_ident;
            type_def_expr = Some fld_elem_type;
            type_def_rep = true;
            type_def_loc = loc;
          } in

          let var_def = {
            Stmt.var_decl = 
              Type.mk_var_decl ~loc ~const:true (Rewriter.ProgUtils.heap_utils_id_ident loc) type_tp_expr;
            var_init = Some (Expr.mk_var ~loc ~typ:fld_elem_type (Rewriter.ProgUtils.get_ra_id ra_qual_ident));
          } in

          let heap_valid_fn_decl = {
            Callable.call_decl_kind = Func;
            call_decl_name = Rewriter.ProgUtils.heap_utils_valid_ident loc;
            call_decl_formals = [
              Type.mk_var_decl ~loc ~const:true (Ident.fresh loc "h") (Type.mk_map loc in_arg_typ type_tp_expr)
            ];
            call_decl_returns = [
              Type.mk_var_decl ~loc ~const:true (Ident.fresh loc "ret") Type.bool
            ];
            call_decl_locals = [];
            call_decl_precond = [];
            call_decl_postcond = [];
            call_decl_is_free = true;
            call_decl_is_auto = false;
            call_decl_loc = loc;
          } in

          let l_var_decl = 
            Type.mk_var_decl ~loc ~const:true (Ident.fresh loc "l") in_arg_typ
          in

          let ra_valid_fn_qual_ident = Rewriter.ProgUtils.get_ra_valid_fn_qual_ident ra_qual_ident in

          let heap_valid_fn = {
            Callable.call_decl = heap_valid_fn_decl;
            call_def = FuncDef { func_body = Some (
              Expr.mk_and (
                Expr.mk_binder ~loc ~typ:Type.bool Forall [l_var_decl] (
                    Expr.mk_app ~loc ~typ:Type.bool (Expr.Var ra_valid_fn_qual_ident) [
                  Expr.mk_maplookup ~loc (Expr.from_var_decl (List.hd_exn heap_valid_fn_decl.call_decl_formals)) (Expr.from_var_decl l_var_decl)
                  ]
                ) ::

                (if is_field then
                  (* Null has no ownership *)
                  [Expr.mk_eq ~loc 
                    (Expr.mk_maplookup ~loc (Expr.from_var_decl (List.hd_exn heap_valid_fn_decl.call_decl_formals)) (Expr.mk_app ~loc ~typ:Type.ref Null []) )
                    (Expr.mk_var ~loc ~typ:type_tp_expr (Rewriter.ProgUtils.get_ra_id ra_qual_ident))
                  ]
                
                else
                  []
                )
              )
            )
            }
          }
          
          in


          let heap_add_chunk_fn_decl = {
            Callable.call_decl_kind = Func;
            call_decl_name = Rewriter.ProgUtils.heap_utils_comp_chunk_ident loc;
            call_decl_formals = [
              Type.mk_var_decl ~loc ~const:true (Ident.fresh loc "x1") type_tp_expr;
              Type.mk_var_decl ~loc ~const:true (Ident.fresh loc "x2") type_tp_expr;
            ];
            call_decl_returns = [
              Type.mk_var_decl ~loc ~const:true (Ident.fresh loc "ret") type_tp_expr;
            ];
            call_decl_locals = [];
            call_decl_precond = [];
            call_decl_postcond = [];
            call_decl_is_free = true;
            call_decl_is_auto = false;
            call_decl_loc = loc;
          } in

          let heap_add_chunk_fn = {
            Callable.call_decl = heap_add_chunk_fn_decl;
            call_def = FuncDef { func_body = Some (
              Expr.mk_app ~loc ~typ:type_tp_expr (Expr.Var (Rewriter.ProgUtils.get_ra_comp_fn_qual_ident ra_qual_ident)) [
                Expr.from_var_decl (List.hd_exn heap_add_chunk_fn_decl.call_decl_formals);
                Expr.from_var_decl (List.nth_exn heap_add_chunk_fn_decl.call_decl_formals 1)
              ]
            )
            }
          } 
        
          in


          let heap_sub_chunk_fn_decl = {
            Callable.call_decl_kind = Func;
            call_decl_name = Rewriter.ProgUtils.heap_utils_frame_chunk_ident loc;
            call_decl_formals = [
              Type.mk_var_decl ~loc ~const:true (Ident.fresh loc "x1") type_tp_expr;
              Type.mk_var_decl ~loc ~const:true (Ident.fresh loc "x2") type_tp_expr;
            ];
            call_decl_returns = [
              Type.mk_var_decl ~loc ~const:true (Ident.fresh loc "ret") type_tp_expr;
            ];
            call_decl_locals = [];
            call_decl_precond = [];
            call_decl_postcond = [];
            call_decl_is_free = true;
            call_decl_is_auto = false;
            call_decl_loc = loc;
          } in

          let heap_sub_chunk_fn = {
            Callable.call_decl = heap_sub_chunk_fn_decl;
            call_def = FuncDef { func_body = Some (
              Expr.mk_app ~loc ~typ:type_tp_expr (Expr.Var (Rewriter.ProgUtils.get_ra_frame_fn_qual_ident ra_qual_ident)) [
                Expr.from_var_decl (List.hd_exn heap_sub_chunk_fn_decl.call_decl_formals);
                Expr.from_var_decl (List.nth_exn heap_sub_chunk_fn_decl.call_decl_formals 1)
              ]
            )
            }
          } 
        
          in

          let heapchunk_compare_fn_decl = {
            Callable.call_decl_kind = Func;
            call_decl_name = Rewriter.ProgUtils.heap_utils_heapchunk_compare_ident loc;
            call_decl_formals = [
              Type.mk_var_decl ~loc ~const:true (Ident.fresh loc "x1") type_tp_expr;
              Type.mk_var_decl ~loc ~const:true (Ident.fresh loc "x2") type_tp_expr;
            ];
            call_decl_returns = [
              Type.mk_var_decl ~loc ~const:true (Ident.fresh loc "ret") Type.bool;
            ];
            call_decl_locals = [];
            call_decl_precond = [];
            call_decl_postcond = [];
            call_decl_is_free = true;
            call_decl_is_auto = false;
            call_decl_loc = loc;
          } in



          let heapchunk_compare_fn = {
            Callable.call_decl = heapchunk_compare_fn_decl;
            call_def = FuncDef { func_body = Some (
              Expr.mk_app ~loc ~typ:type_tp_expr (Expr.Var ra_valid_fn_qual_ident) [
                Expr.mk_app ~loc ~typ:type_tp_expr (Expr.Var (QualIdent.from_ident heap_sub_chunk_fn_decl.call_decl_name)) [
                  Expr.from_var_decl (List.hd_exn heapchunk_compare_fn_decl.call_decl_formals);
                  Expr.from_var_decl (List.nth_exn heapchunk_compare_fn_decl.call_decl_formals 1)
                ]
              ]
            )
            }
          } 
        
          in


          Rewriter.return [
            Module.SymbolDef (Module.TypeDef type_def);
            SymbolDef (Module.VarDef var_def);
            SymbolDef (Module.CallDef heap_valid_fn);
            SymbolDef (Module.CallDef heap_add_chunk_fn);
            SymbolDef (Module.CallDef heap_sub_chunk_fn);
            SymbolDef (Module.CallDef heapchunk_compare_fn);
          ]
          
          
        in
        
        Rewriter.return (Module.ModDef { mod_decl; mod_def; }) 

  let rewrite_add_field_utils (symbol: Module.symbol) : Module.symbol Rewriter.t =
    let open Rewriter.Syntax in
    match symbol with
    | FieldDef f ->
      let* utils_module = 
        let ra_qual_ident = Rewriter.ProgUtils.field_get_ra_qual_iden f in
        let mod_ident = Rewriter.ProgUtils.field_utils_module_ident f.field_loc f.field_name in
        generate_utils_module ~is_field:true mod_ident ra_qual_ident f.field_loc
      
      in
        
      let* _ = Rewriter.introduce_typecheck_symbol ~loc:f.field_loc ~f:Typing.process_symbol utils_module in

      Rewriter.return symbol

  | _ -> Rewriter.return symbol

  let rewrite_add_pred_utils (c: Callable.t) : Callable.t Rewriter.t = 
    let open Rewriter.Syntax in
    match c.call_decl.call_decl_kind with
    | Pred | Invariant -> 
      let loc = c.call_decl.call_decl_loc in
      let pred_ret_type = Type.mk_prod c.call_decl.call_decl_loc (List.map c.call_decl.call_decl_returns ~f:(fun var_decl -> var_decl.var_type)) in

      let* pred_ret_type_module = Rewriter.ProgUtils.intros_type_module ~loc:c.call_decl.call_decl_loc ~f:Typing.process_symbol pred_ret_type in

      let mod_inst_type, mod_inst_def_ra = match c.call_decl.call_decl_kind with
        | Pred -> Predefs.lib_cancellative_ra_mod_qual_ident, Predefs.lib_countAgreeRA_mod_qual_ident
        | Invariant -> Predefs.lib_lattice_ra_mod_qual_ident, Predefs.lib_agree_mod_qual_ident
        | _ -> Error.internal_error loc "Expected a predicate or invariant"
      
      in

      let instantiated_pred_heap_ra = 
        Module.ModInst {
          mod_inst_name = Rewriter.ProgUtils.pred_to_ra_mod_ident ~loc c.call_decl.call_decl_name;
          mod_inst_type = mod_inst_type;
          mod_inst_def = Some (mod_inst_def_ra, [pred_ret_type_module]);
          mod_inst_is_interface = false;
          mod_inst_loc = loc;
        } in

      let* pred_heap_ra = Rewriter.introduce_typecheck_symbol ~loc ~f:Typing.process_symbol instantiated_pred_heap_ra in

      Logs.debug (fun m -> m "Generated pred heap RA module: %a" Module.pr_symbol instantiated_pred_heap_ra);

      let in_arg_typ = Type.mk_prod c.call_decl.call_decl_loc (List.map c.call_decl.call_decl_formals ~f:(fun var_decl -> var_decl.var_type)) in

      let* utils_module = 
        generate_utils_module ~is_field:false (Rewriter.ProgUtils.pred_utils_module_ident loc c.call_decl.call_decl_name) pred_heap_ra ~in_arg_typ loc
      in

      let* _ = Rewriter.introduce_typecheck_symbol ~loc ~f:Typing.process_symbol utils_module in

      Rewriter.return c

    | _ -> Rewriter.return c

  let rewrite_add_atomics_utils (c: Callable.t) : Callable.t Rewriter.t = 
    let open Rewriter.Syntax in
    match c.call_decl.call_decl_kind with
    | Proc ->
      if not (Callable.is_atomic c.call_decl) then
        Rewriter.return c
      else
        let loc = c.call_decl.call_decl_loc in

        let proc_concrete_args_typ = Type.mk_prod c.call_decl.call_decl_loc (List.filter_map c.call_decl.call_decl_formals ~f:(fun var_decl -> if var_decl.var_implicit then None else Some var_decl.var_type)) in

        let* proc_conrete_args_type_module = Rewriter.ProgUtils.intros_type_module ~loc:c.call_decl.call_decl_loc ~f:Typing.process_symbol proc_concrete_args_typ in

        let proc_ret_type = Type.mk_prod c.call_decl.call_decl_loc (List.map c.call_decl.call_decl_returns ~f:(fun var_decl -> var_decl.var_type)) in

        let* proc_ret_type_module = Rewriter.ProgUtils.intros_type_module ~loc:c.call_decl.call_decl_loc ~f:Typing.process_symbol proc_ret_type in

        let instantiated_au_proc_heap_ra = 
          Module.ModInst {
            mod_inst_name = Rewriter.ProgUtils.au_to_ra_mod_ident ~loc c.call_decl.call_decl_name;
            mod_inst_type = Predefs.lib_ra_mod_qual_ident;
            mod_inst_def = Some (Predefs.lib_atomic_token_ra_mod_qual_ident, [proc_conrete_args_type_module; proc_ret_type_module]);
            mod_inst_is_interface = false;
            mod_inst_loc = loc;
          } in

        let* au_proc_heap_ra = Rewriter.introduce_typecheck_symbol ~loc ~f:Typing.process_symbol instantiated_au_proc_heap_ra in

        Logs.debug (fun m -> m "Generated au heap RA module: %a" Module.pr_symbol instantiated_au_proc_heap_ra);

        let in_arg_typ = Type.atomic_token in

        let* utils_module = 
          generate_utils_module ~is_field:false (Rewriter.ProgUtils.au_utils_module_ident loc c.call_decl.call_decl_name) au_proc_heap_ra ~in_arg_typ loc
        in

        let* _ = Rewriter.introduce_typecheck_symbol ~loc ~f:Typing.process_symbol utils_module in

        Rewriter.return c

    | _ ->
      Rewriter.return c


  let introduce_heaps_in_stmts ~loc ~fields_list ~preds_list ~au_preds_list body : Stmt.t Rewriter.t =
    let open Rewriter.Syntax in
    (* TODO: Introduce variables of right types for predHeaps *)

    let* field_heap_var_defs = Rewriter.List.map fields_list ~f:(fun field_name -> 
      let* field_symbol = Rewriter.find_and_reify (Loc.dummy) field_name in

      let field_elem_type = match field_symbol with
        | FieldDef f -> 
          (match f.field_type with
          | App (Fld, [tp_expr], _) -> tp_expr
          | _ -> Error.type_error f.field_loc "Expected field identifier.")
        | _ -> Error.error (Loc.dummy) "Expected a field_def"

      in

      (* Done so that Ident is aware of this name being used; prevents the same name from being generated again during SSA transform *)
      let _ = Ident.fresh loc (field_heap_name field_name).ident_name in

      let (heap_var_decl: var_decl) = {
        var_name = field_heap_name field_name;
        var_loc = loc;
        var_type = Type.mk_map loc Type.ref field_elem_type;
        var_const = false;
        var_ghost = true;
        var_implicit = false;
      } in

      let* field_utils_id = Rewriter.ProgUtils.get_field_utils_id (Stmt.loc body) field_name in

      let assume_expr1 = 
        let l_var = Type.{ 
          var_name = Ident.fresh (Stmt.loc body) "l"; 
          var_loc = (Stmt.loc body); 
          var_type = Type.ref; 
          var_const = false; 
          var_ghost = false; 
          var_implicit = false; } 
        in

        let l_expr = Expr.mk_var ~typ:l_var.var_type (QualIdent.from_ident l_var.var_name) in
        
        Expr.mk_binder Forall [l_var] (Expr.mk_eq 
          (Expr.mk_maplookup (Expr.from_var_decl heap_var_decl) l_expr)
          field_utils_id
        )
      in

      let _ = Ident.fresh loc (field_heap_name2 field_name).ident_name in

      let (heap_var_decl2: var_decl) = {
        var_name = field_heap_name2 field_name;
        var_loc = loc;
        var_type = Type.mk_map loc Type.ref field_elem_type;
        var_const = false;
        var_ghost = true;
        var_implicit = false;
      } in

      let assume_expr2 = 
        let l_var = { 
          Type.var_name = Ident.fresh (Stmt.loc body) "l"; 
          var_loc = loc; 
          var_type = Type.ref; 
          var_const = false; 
          var_ghost = false; 
          var_implicit = false; } 
        in

        let l_expr = Expr.mk_var ~typ:l_var.var_type (QualIdent.from_ident l_var.var_name) in
        
        Expr.mk_binder Forall [l_var] (Expr.mk_eq 
          (Expr.mk_maplookup (Expr.from_var_decl heap_var_decl2) l_expr)
          field_utils_id
        )
      in

      Rewriter.return ({ Stmt.var_decl = heap_var_decl; var_init = None }, { Stmt.var_decl = heap_var_decl2; var_init = None }, Stmt.mk_assume_expr ~loc assume_expr1, Stmt.mk_assume_expr ~loc:(Stmt.loc body) assume_expr2)

    ) in

    let* pred_heap_var_defs = Rewriter.List.map preds_list ~f:(fun pred_name -> 
      let* pred_heap_elem_type_qual_ident = Rewriter.ProgUtils.get_pred_utils_rep_type loc pred_name in

      let pred_heap_elem_type = Type.mk_var loc pred_heap_elem_type_qual_ident in

      let* pred_in_types = Rewriter.ProgUtils.pred_in_types pred_name in

      (* Done so that Ident is aware of this name being used; prevents the same name from being generated again during SSA transform *)
      let _ = Ident.fresh loc (pred_heap_name pred_name).ident_name in

      let (heap_var_decl: var_decl) = {
        var_name = pred_heap_name pred_name;
        var_loc = loc;
        var_type = Type.mk_map loc (Type.mk_prod loc pred_in_types) pred_heap_elem_type;
        var_const = false;
        var_ghost = true;
        var_implicit = false;
      } in

      let* pred_utils_id = Rewriter.ProgUtils.get_pred_utils_id (Stmt.loc body) pred_name in

      let assume_expr1 = 
        let in_var = { 
          Type.var_name = Ident.fresh (Stmt.loc body) "in"; 
          var_loc = (Stmt.loc body); 
          var_type = (Type.mk_prod loc pred_in_types); 
          var_const = false; 
          var_ghost = false; 
          var_implicit = false; } 
        in

        let in_var_expr = Expr.mk_var ~typ:in_var.var_type (QualIdent.from_ident in_var.var_name) in
        
        Expr.mk_binder Forall [in_var] (Expr.mk_eq 
        
          (Expr.mk_maplookup (Expr.from_var_decl heap_var_decl) in_var_expr)
          pred_utils_id
        )
      in

      let _ = Ident.fresh loc (pred_heap_name2 pred_name).ident_name in

      let (heap_var_decl2: var_decl) = {
        var_name = pred_heap_name2 pred_name;
        var_loc = loc;
        var_type = Type.mk_map loc (Type.mk_prod loc pred_in_types) pred_heap_elem_type;
        var_const = false;
        var_ghost = true;
        var_implicit = false;
      } in

      let assume_expr2 = 
        let in_var = { 
          Type.var_name = Ident.fresh (Stmt.loc body) "in"; 
          var_loc = (Stmt.loc body); 
          var_type = (Type.mk_prod loc pred_in_types); 
          var_const = false; 
          var_ghost = false; 
          var_implicit = false; } 
        in

        let in_var_expr = Expr.mk_var ~typ:in_var.var_type (QualIdent.from_ident in_var.var_name) in
        
        Expr.mk_binder Forall [in_var] (Expr.mk_eq 
          (Expr.mk_maplookup (Expr.from_var_decl heap_var_decl2) in_var_expr)
          pred_utils_id
        )
      in

      Rewriter.return ({ Stmt.var_decl = heap_var_decl; var_init = None }, { Stmt.var_decl = heap_var_decl2; var_init = None }, Stmt.mk_assume_expr ~loc assume_expr1, Stmt.mk_assume_expr ~loc:(Stmt.loc body) assume_expr2)
      
    ) in

    let* au_heap_var_defs = Rewriter.List.map au_preds_list ~f:(fun call_name -> 
      let* au_heap_elem_type_qual_ident = Rewriter.ProgUtils.get_au_utils_rep_type loc call_name in

      let au_heap_elem_type = Type.mk_var loc au_heap_elem_type_qual_ident in

      (* Done so that Ident is aware of this name being used; prevents the same name from being generated again during SSA transform *)
      let _ = Ident.fresh loc (au_heap_name call_name).ident_name in

      let (heap_var_decl: var_decl) = {
        var_name = au_heap_name call_name;
        var_loc = loc;
        var_type = Type.mk_map loc Type.atomic_token au_heap_elem_type;
        var_const = false;
        var_ghost = true;
        var_implicit = false;
      } in

      let* au_utils_id = Rewriter.ProgUtils.get_au_utils_id (Stmt.loc body) call_name in

      let assume_expr1 = 
        let in_var = { 
          Type.var_name = Ident.fresh (Stmt.loc body) "tok"; 
          var_loc = (Stmt.loc body); 
          var_type = Type.atomic_token; 
          var_const = false; 
          var_ghost = false; 
          var_implicit = false; } 
        
        in

        let in_var_expr = Expr.mk_var ~typ:in_var.var_type (QualIdent.from_ident in_var.var_name) in
        
        Expr.mk_binder Forall [in_var] (Expr.mk_eq 
        
          (Expr.mk_maplookup (Expr.from_var_decl heap_var_decl) in_var_expr)
          au_utils_id
        )
      in

      let _ = Ident.fresh loc (au_heap_name2 call_name).ident_name in

      let (heap_var_decl2: var_decl) = {
        var_name = au_heap_name2 call_name;
        var_loc = loc;
        var_type = Type.mk_map loc Type.atomic_token au_heap_elem_type;
        var_const = false;
        var_ghost = true;
        var_implicit = false;
      } in

      let assume_expr2 = 
        let in_var = { 
          Type.var_name = Ident.fresh (Stmt.loc body) "in"; 
          var_loc = (Stmt.loc body); 
          var_type = Type.atomic_token; 
          var_const = false; var_ghost = false; 
          var_implicit = false; } 
        in

        let in_var_expr = Expr.mk_var ~typ:in_var.var_type (QualIdent.from_ident in_var.var_name) in
        
        Expr.mk_binder Forall [in_var] (Expr.mk_eq 
          (Expr.mk_maplookup (Expr.from_var_decl heap_var_decl2) in_var_expr)
          au_utils_id
        )
      in

      Rewriter.return ({ Stmt.var_decl = heap_var_decl; var_init = None }, { Stmt.var_decl = heap_var_decl2; var_init = None }, Stmt.mk_assume_expr ~loc assume_expr1, Stmt.mk_assume_expr ~loc:(Stmt.loc body) assume_expr2)
      
    ) in

    let* init_assumes = Rewriter.List.fold_left ~init:[] (field_heap_var_defs @ pred_heap_var_defs @ au_heap_var_defs) ~f:(fun assumes (heap_var_decl, heap_var_decl2, assume_stmt1, assume_stmt2) -> 
      Logs.debug (fun m -> m "Rewrites.HeapsExplicitTrnsl.introduce_heaps_in_stmts: heap_var_decl: %a; heap_var_decl2: %a" Ident.pr heap_var_decl.var_decl.var_name Ident.pr heap_var_decl2.var_decl.var_name );
      let* _ = Rewriter.introduce_symbol (Module.VarDef heap_var_decl) in
      let+ _ = Rewriter.introduce_symbol (Module.VarDef heap_var_decl2) in
      assume_stmt1 :: assume_stmt2 :: assumes

    ) in

    (* Rewriter.return (Stmt.mk_block_stmt ~loc (init_assumes @ [body])) *)
    Rewriter.return body


  type expr_match = {
    var_decl: var_decl;
    expr: expr option;
  }

  let match_up_expr (expr1: expr) (expr2: expr) (vars: var_decl list) : ((var_decl * expr) ident_map) option =
    (* expr1 is the expr with vars; expr2 is the one to be matched against. So expr1 is allowed to have more existentials than expr2. For first implementation, expr2 is not allowed to have any existentials for now *)

    (* Return value of None represents that the expressions did not match up *)

    (* Running example: 
            expr1: forall a :: f(a) ==> exists b :: e(a, b) 
            expr2: forall a1 :: f(a1) ==> e(a1, v)

            vars: [b]
    *)

    let rec match_up_expr (expr1: expr) (expr2: expr) (var_map: expr_match ident_map) : (expr_match ident_map) option  =

    if Type.((Expr.to_type expr1) <> (Expr.to_type expr2)) then
      None
    else

    match expr1, expr2 with
    | Binder (Compr, v_d1, _, e1, _), Binder (Compr, v_d2, _, e2, _)
    | Binder (Forall, v_d1, _, e1, _), Binder (Forall, v_d2, _, e2, _) ->
      if not (Int.equal (List.length v_d1) (List.length v_d2)) then 
        None
      else
        let typ_check = List.for_all2_exn v_d1 v_d2 ~f:(fun vd1 vd2 -> Type.equal vd1.var_type vd2.var_type) in

        if not typ_check then
          None
        else

        let renaming_map = List.fold2_exn v_d1 v_d2 ~init:(Map.empty (module QualIdent)) ~f:(fun renam_map vd1 vd2 ->
          Map.add_exn renam_map ~key:(QualIdent.from_ident vd2.var_name) ~data:(Expr.from_var_decl vd1)
          
        ) in
        
        (* renaming expr2 to use the same universal quants as expr1 *)
        let e2 = Expr.alpha_renaming e2 renaming_map in

        match_up_expr e1 e2 var_map 

    | Binder (Exists, v_d1, _, e1, _), e2 ->
      let var_map = List.fold v_d1 ~init:var_map ~f:(fun var_map vd1 -> 
        match Map.find var_map vd1.var_name with
        | Some _ -> var_map
        | None -> Error.error (Expr.to_loc expr1) "Unexpected existential quantifier in expr1; expected all existentials to be declared in var_map"
      ) in

        match_up_expr e1 e2 var_map

    | App (constr1, exprs1, _), App (constr2, exprs2, _) ->
      begin match constr1 with
      | Var qual_ident when 
          (List.exists (Map.keys var_map) ~f:(fun iden -> QualIdent.equal (QualIdent.from_ident iden) qual_ident))  
        -> (
        let var_iden = QualIdent.to_ident qual_ident in
        

        let expr_match = (Map.find_exn var_map var_iden) in
        match expr_match.expr with
        | None ->
          let var_map = Map.set var_map ~key:var_iden ~data:{ expr_match with expr = Some expr2} in
          
          Some var_map

        | Some e ->
          if Expr.alpha_equal e expr2 then
            Some var_map
          else
            None
      )

      | _ -> 
        if Expr.equal_constr constr1 constr2 then
          if List.length exprs1 <> List.length exprs2 then
            None
          else
            let var_map_optn = List.fold2_exn exprs1 exprs2 ~init:(Some var_map) ~f:(fun var_map_optn e1 e2 -> 
              Option.flat_map var_map_optn ~f:(fun var_map -> match_up_expr e1 e2 var_map)
            ) in

            var_map_optn
        
        else
          None
      end


    | _ -> None

    in

    let var_map_optn = match_up_expr expr1 expr2 (Map.of_alist_exn (module Ident) (List.map vars ~f:(fun var_decl -> (var_decl.var_name, { var_decl; expr = None })))) in

    match var_map_optn with
    | Some var_map -> 
      Some (Map.map var_map ~f:(fun { var_decl; expr } -> 
        match expr with
        | Some e -> (var_decl, e)
        | None -> Error.error (Expr.to_loc expr1) "Expected all variables to be matched up"
      ))
    | None -> None
  
  module TrnslInhale = struct 
    let rec skolemize_inhale_expr (universal_quants: universal_quants) (subst: expr qual_ident_map) (expr: expr) : expr Rewriter.t =
      let open Rewriter.Syntax in

      let generate_skolem_function (universal_quants: universal_quants) (var_decl: var_decl) : expr Rewriter.t = 
        let univ_quants_list = universal_quants.univ_vars in
        (* univ_quants_list computed here to keep the ordering on keys constant for the construction *)
        if List.is_empty univ_quants_list then
          let var_decl = { var_decl with var_name = Ident.fresh var_decl.var_loc var_decl.var_name.ident_name } in
          let symbol = Module.VarDef { var_decl; var_init = None } in
          let* _ = Rewriter.introduce_symbol symbol in

          Rewriter.return (Expr.mk_var ~typ:var_decl.var_type (QualIdent.from_ident var_decl.var_name))

        else
          let map_dom_type = Type.mk_prod (var_decl.var_loc) (List.map univ_quants_list ~f:(fun (_, v_d) -> v_d.var_type)) in
          let var_type = Type.mk_map (var_decl.var_loc) map_dom_type var_decl.var_type in

          let var_decl = { var_decl with var_name = Ident.fresh var_decl.var_loc ("skolem_" ^ var_decl.var_name.ident_name); var_type = var_type } in
          let symbol = Module.VarDef { var_decl; var_init = None } in
          let* _ = Rewriter.introduce_symbol symbol in

          let tuple_expr = Expr.mk_tuple (List.map univ_quants_list ~f:(fun (_, v_d) -> Expr.mk_var ~typ:v_d.var_type (QualIdent.from_ident v_d.var_name))) in

          Rewriter.return (Expr.mk_maplookup (Expr.mk_var ~typ:var_decl.var_type (QualIdent.from_ident var_decl.var_name)) tuple_expr)
          (* let skolem_fn_ident = Ident.fresh (Expr.to_loc expr) ("$skolem_" ^ (Ident.to_string var_decl.var_name)) in

          let formal_var_decls = 
            List.map univ_quants_list ~f:(fun (v, v_decl) -> 
              { 
                Type.var_name = v_decl.var_name; 
                var_loc = Expr.to_loc expr; 
                var_type = v_decl.var_type; 
                var_const = true; 
                var_ghost = false; 
                var_implicit = false; 
              }
            )

          in
          let ret_var_decl = {
            Type.var_name = Ident.fresh (Expr.to_loc expr) ("ret_" ^ (Ident.to_string var_decl.var_name));
            var_loc = Expr.to_loc expr;
            var_type = var_decl.var_type;
            var_const = true;
            var_ghost = false;
            var_implicit = false;
          } in
    
          let call_decl = {
            Callable.call_decl_kind = Func;
            call_decl_name = skolem_fn_ident;
            call_decl_formals = formal_var_decls;
            call_decl_returns = [ret_var_decl];
            call_decl_locals = [];
            call_decl_precond = [];
            call_decl_postcond = [];
            call_decl_loc = Expr.to_loc expr;
          }
            
          in

          let* skolem_fn_qual_ident = 
            let+ module_qual_ident = Rewriter.current_module_name in
      
            QualIdent.append module_qual_ident skolem_fn_ident
      
          in
        
          let callable = Callable.{ call_decl; call_def = FuncDef { func_body = None;} }

          
          in

          let symbol = Module.CallDef callable in

          let* _ = Rewriter.introduce_typecheck_symbol ~loc:(Expr.to_loc expr) ~f:(Typing.process_symbol) symbol in

          let ret_expr = Expr.mk_app (Expr.Var skolem_fn_qual_ident) (List.map univ_quants_list ~f:(fun (v, _) -> Expr.mk_var (QualIdent.from_ident v))) in

          Rewriter.return ret_expr *)
      in

      match expr with
      | Binder (Forall, var_decls, trgs, e, e_attr) ->
        let universal_quants = 
          let new_quants = List.map var_decls ~f:(fun var_decl -> (var_decl.var_name, var_decl)) in
          { universal_quants with 
            univ_vars = universal_quants.univ_vars @ new_quants
          }  
        in
          
          (* List.fold var_decls ~init:universal_quants ~f:(fun map var_decl -> 
          Map.add_exn map ~key:var_decl.var_name ~data:var_decl
        in *)
        let* e = skolemize_inhale_expr universal_quants subst e in

        Rewriter.return Expr.(Binder (Forall, var_decls, trgs, e, e_attr))

      | Binder (Exists, var_decls, trgs, e, e_attr) ->
        let* subst =
          Rewriter.List.fold_left var_decls ~init:subst ~f:(fun map var_decl -> 
            let* (new_expr: expr) = generate_skolem_function universal_quants var_decl in
            Rewriter.return (Map.add_exn map ~key:(QualIdent.from_ident var_decl.var_name) ~data:new_expr)
          )

        in
        let* e = skolemize_inhale_expr universal_quants subst e in

        Logs.debug (fun m -> m "Rewrites.HeapsExplicitTrnsl.TrnslInhale.skolemize_inhale_expr: found existentials:  e: %a" Expr.pr e);
        Rewriter.return e

      | _ -> 
        let* expr = Rewriter.Expr.descend expr ~f:(skolemize_inhale_expr universal_quants subst) in

        let expr = Expr.alpha_renaming expr subst in
        (* This will cause the renaming to be done at each step of descend, but renaming should be idempotent, so that should be okay *)

        Logs.debug (fun m -> m "Rewrites.HeapsExplicitTrnsl.TrnslInhale.skolemize_inhale_expr: e: %a" Expr.pr expr);
        Rewriter.return expr
    

    let rec rewriter_skolemize_inhale_stmts (stmt: Stmt.t) : Stmt.t Rewriter.t = 
      let open Rewriter.Syntax in
      match stmt.stmt_desc with
      | Basic (Spec (spec_kind, spec)) ->
        (match spec_kind with
        | Inhale ->
          let* e = skolemize_inhale_expr {univ_vars = []; triggers = []} (Map.empty (module QualIdent)) spec.spec_form in

          let spec = { spec with spec_form = e } in

          Rewriter.return {stmt with stmt_desc = Basic (Spec (spec_kind, spec))}

        | _ -> Rewriter.return stmt)


      | _ -> Rewriter.Stmt.descend stmt ~f:rewriter_skolemize_inhale_stmts


    let rec rewriter_eliminate_binds_for_inhale (stmt: Stmt.t) : (Stmt.t, expr option) Rewriter.t_ext =
      let open Rewriter.Syntax in
      match stmt.stmt_desc with
      | Basic (Spec (Inhale, spec)) ->
        let* () = Rewriter.set_user_state (Some spec.spec_form) in
        Rewriter.return stmt

      | Basic (Bind bind_desc) ->
        let* prev_expr = Rewriter.current_user_state in
        let* () = Rewriter.set_user_state None in

        begin match prev_expr with
        | None ->
          Rewriter.return stmt

        | Some prev_expr ->
          (* Logs.debug (fun m -> m "Rewrites.HeapsExplicitTrnsl.TrnslInhale.rewriter_eliminate_binds_for_inhale: bind_desc: %a; prev_expr: %a" Stmt.pr stmt Expr.pr prev_expr); *)

          let* bind_lhs_var_decls = Rewriter.List.map bind_desc.bind_lhs ~f:(fun var -> 
            let* symbol = Rewriter.find_and_reify (Expr.to_loc bind_desc.bind_rhs) (Expr.to_qual_ident var) in
            match symbol with
            | VarDef v -> Rewriter.return v.var_decl
            | _ -> Error.error (Expr.to_loc bind_desc.bind_rhs) "Expected a variable declaration"
          ) in

          match match_up_expr bind_desc.bind_rhs prev_expr bind_lhs_var_decls with
          | None -> Rewriter.return stmt
          | Some var_map ->
            let assign_stmts = List.map bind_lhs_var_decls ~f:(fun var_decl -> 
              let _, rhs = Map.find_exn var_map (var_decl.var_name) in

              Stmt.mk_assign ~loc:(Expr.to_loc bind_desc.bind_rhs) [(Expr.from_var_decl var_decl)] rhs
            ) in

            Rewriter.return (Stmt.mk_block_stmt ~loc:(Expr.to_loc bind_desc.bind_rhs) (assign_stmts))

        end

      | _ -> 
        let* () = Rewriter.set_user_state None in
        Rewriter.Stmt.descend stmt ~f:rewriter_eliminate_binds_for_inhale

    let rec trnsl_inhale_expr ?cmnt ~loc (expr: expr) : Stmt.t Rewriter.t =
      trnsl_inhale_a ?cmnt ~loc [] expr
      

    and trnsl_inhale_a ?cmnt ~loc (conds: conditions) (expr: expr): Stmt.t Rewriter.t =
      let open Rewriter.Syntax in
  
      match expr with
      | App (Ite, [c; e1; e2], _) ->
        let* stmt1 = trnsl_inhale_a ?cmnt ~loc (c :: conds) e1 in
  
        let not_c = Expr.mk_not ~loc:(Expr.to_loc c) c in
        let* stmt2 = trnsl_inhale_a ?cmnt ~loc (not_c :: conds) e2 in
        
        Rewriter.return (Stmt.mk_block_stmt ~loc [stmt1; stmt2])
      | App (Impl, [c; e2], _) ->
        trnsl_inhale_a ?cmnt ~loc (c :: conds) e2
  
      | App (And, e_list, _) ->
        let* stmts_list = Rewriter.List.map e_list ~f:(fun e -> trnsl_inhale_a ?cmnt ~loc conds e) in
        
        Rewriter.return (Stmt.mk_block_stmt ~loc stmts_list)
        
  
      | _ -> trnsl_inhale_a2 ?cmnt ~loc {univ_vars = []; triggers = []} conds expr

    and trnsl_inhale_a2 ?cmnt ~loc (universal_quants: universal_quants) (conds: conditions) (expr: expr): Stmt.t Rewriter.t =
      let open Rewriter.Syntax in
  
      match expr with
      | App (And, e_list, _) ->
        let* stmts_list = Rewriter.List.map e_list ~f:(fun e -> trnsl_inhale_a2 ?cmnt ~loc universal_quants conds e) in
  
        Rewriter.return (Stmt.mk_block_stmt ~loc stmts_list)
  
      | Binder (Forall, var_decls, trgs, e, _) ->
        let universal_quants = 
          let new_quants = List.map var_decls ~f:(fun var_decl -> (var_decl.var_name, var_decl)) in
          {  
            univ_vars = universal_quants.univ_vars @ new_quants;
            triggers = match universal_quants.triggers with
            | [] -> trgs
            | _ -> List.concat_map universal_quants.triggers ~f:(fun trigs -> List.map trgs ~f:(fun trg -> trigs @ trg));
          }  
        in
          
          (* List.fold var_decls ~init:universal_quants ~f:(fun map var_decl -> 
          Map.add_exn map ~key:var_decl.var_name ~data:var_decl
        ) in *)
        let* stmt = trnsl_inhale_a2 ?cmnt ~loc universal_quants conds e in
  
        Rewriter.return stmt
  
      | _ -> trnsl_inhale_a2' ?cmnt ~loc universal_quants conds expr


    and trnsl_inhale_a2' ?cmnt ~loc (universal_quants: universal_quants) (conds: conditions) (expr: expr): Stmt.t Rewriter.t =
      let open Rewriter.Syntax in
  
      match expr with
      | App (And, e_list, _) ->
        let* stmts_list = Rewriter.List.map e_list ~f:(fun e -> trnsl_inhale_a2' ?cmnt ~loc universal_quants conds e) in

        Rewriter.return (Stmt.mk_block_stmt ~loc stmts_list)
        
      | App (Impl, [c; e2], _) ->
        trnsl_inhale_a2' ?cmnt ~loc universal_quants (c :: conds) e2
      
      | App (Ite, [c; e1; e2], _) ->
        let* stmt1 = trnsl_inhale_a2' ?cmnt ~loc universal_quants (c :: conds) e1 in
  
        let not_c = Expr.mk_not ~loc:(Expr.to_loc c) c in
        let* stmt2 = trnsl_inhale_a2' ?cmnt ~loc universal_quants (not_c :: conds) e2 in
        
        Rewriter.return (Stmt.mk_block_stmt ~loc [stmt1; stmt2])
  
      | _ -> trnsl_inhale_a0 ?cmnt ~loc universal_quants conds expr

    and trnsl_inhale_a0 ?cmnt ~loc (universal_quants: universal_quants) (conds: conditions) (expr: expr): Stmt.t Rewriter.t =
      let open Rewriter.Syntax in

      let univ_quants_list = universal_quants.univ_vars in
      let univ_vars_list = List.map univ_quants_list ~f:(fun (var, var_decl) -> var_decl) in

      match expr with
      | App (And, e_list, _) ->
        let* stmts_list = Rewriter.List.map e_list ~f:(fun e -> trnsl_inhale_a0 ?cmnt ~loc universal_quants conds e) in
          
        Rewriter.return (Stmt.mk_block_stmt ~loc stmts_list)

  
      | App (Own, [e1; e2; e3], _) -> begin    
        (* forall a, b, c :: m1(a, b, c) ==> own(f1(a, b, c), field, f2(a, b, c))
  
        ===>
  
        // asserting injectivity of functions
        assert forall a, b, c, a', b', c' :: m1(a, b, c) && m1(a', b', c') ==> f1(a, b, c) == f1(a', b', c') ==> (a == a' && b == b' && c == c')
  
        havoc(field$Heap2);
  
        assert forall l: Ref :: 
          forall a, b, c :: m1(a,b,c) && l == f1(a, b, c) ?
              field$Heap2[l] == field.comp( field$Heap[l], f2(a, b, c) ) :
            field$Heap2[l] == field$Heap[l]
  
        field$Heap := field$Heap2
        assume field.valid(field$Heap)
        
        *)

        let field_type = match Expr.to_type e2 with
          | App (Fld, [tp_expr], _) -> tp_expr
          | _ -> Error.type_error (Expr.to_loc e2) "Expected field identifier."
        in
  
        let field_name = (Expr.to_qual_ident e2) in
        let field_heap_name = field_heap_name field_name in
        let field_heap_qual_ident = QualIdent.from_ident field_heap_name in
        let field_heap_expr = Expr.mk_var ~typ:(Type.mk_map (Expr.to_loc e2) Type.ref field_type) field_heap_qual_ident in
  
        let field_heap2_name = field_heap_name2 field_name in
        let field_heap2_qual_ident = QualIdent.from_ident field_heap2_name in
        let field_heap2_expr = Expr.mk_var ~typ:(Type.mk_map (Expr.to_loc e2) Type.ref field_type) field_heap2_qual_ident in

        let* (field_heapchunk_operator: qual_ident) = 
          Rewriter.ProgUtils.get_field_utils_comp (Expr.to_loc e2) field_name
        in

        let* (field_heap_valid_fn: qual_ident) = 
          Rewriter.ProgUtils.get_field_utils_valid (Expr.to_loc e2) field_name
        in

        let havoc_stmt = Stmt.mk_havoc ~loc field_heap2_qual_ident in
        let assume_stmt = 
          let l_var = Type.{ var_name = Ident.fresh (Expr.to_loc expr) "l"; var_loc = Expr.to_loc expr; 
          var_type = Type.ref; var_const = false; var_ghost = false; var_implicit = false; } in

          let l_expr = Expr.mk_var ~typ:l_var.var_type (QualIdent.from_ident l_var.var_name) in

          let l_eq_e1_expr = (Expr.mk_eq l_expr e1) in
          
          Stmt.mk_assume_expr ~loc ~cmnt:(Some ((match cmnt with | None -> "" | Some cmnt -> (cmnt ^ "\n")) ^  "inhale: " ^ (Stdlib.Format.asprintf "%a" Expr.pr (Expr.mk_binder Forall univ_vars_list (Expr.mk_impl (Expr.mk_and conds) expr)))))

          (Expr.mk_binder ~trigs:[[Expr.mk_maplookup ~loc field_heap2_expr l_expr]; [Expr.mk_maplookup ~loc field_heap_expr l_expr]]
          
          ~loc ~typ:Type.bool Forall [l_var] 
            (Expr.mk_binder ~loc ~typ:Type.bool Forall univ_vars_list
              (Expr.mk_app ~loc ~typ:Type.bool Expr.Ite [

                (* m1(a,b,c) && l == f1(a, b, c) *)
                Expr.mk_and ~loc (l_eq_e1_expr :: conds);

                (* field$Heap2[l] == field.comp( field$Heap[l], f2(a, b, c) ) *)
                Expr.mk_eq ~loc (Expr.mk_maplookup ~loc field_heap2_expr l_expr)
                  (Expr.mk_app ~loc ~typ:field_type 
                    (Expr.Var field_heapchunk_operator)  [
                      Expr.mk_maplookup ~loc field_heap_expr l_expr;
                      e3;
                    ] );

            
                (* field$Heap2[l] == field$Heap[l] *)
                Expr.mk_eq ~loc (Expr.mk_maplookup ~loc field_heap2_expr l_expr) 
                  (Expr.mk_maplookup ~loc field_heap_expr l_expr);
              ])
            )
          )
        in

        (* field$Heap := field$Heap2 *)
        let eq_stmt = Stmt.mk_assign ~loc [field_heap_expr] field_heap2_expr in
        
        (* let* field_valid_fn = Rewriter.ProgUtils.get_field_utils_valid (Expr.to_loc expr) (Expr.to_qual_ident e2) in
        let heap_valid_stmt = Stmt.mk_assert_expr ~loc 
          (Expr.mk_app ~loc ~typ:Type.bool (Expr.Var field_valid_fn) [field_heap_expr])

        in *)

        let assume_heap_valid = Stmt.mk_assume_expr ~loc 
          (Expr.mk_app ~loc ~typ:Type.bool (Expr.Var field_heap_valid_fn) [field_heap_expr]) 
        
        in

        let* injectivity_assertion = generate_injectivity_assertions universal_quants conds e1 in

        let stmts_list = match univ_quants_list with
        | [] -> []
        | _ -> [injectivity_assertion]

        in

        let stmts_list = stmts_list @ [havoc_stmt; assume_stmt; eq_stmt; assume_heap_valid] in

        let stmt = Stmt.mk_block_stmt ~loc stmts_list in

        Rewriter.return stmt
      end

      | App (AUPred call_qual_ident, token :: args, _) | App (AUPredCommit call_qual_ident, token :: args, _) ->
        Logs.debug (fun m -> m "Rewrites.HeapsExplicitTrnsl.TrnslInhale.trnsl_inhale_a0: expr: %a" Expr.pr expr);
        let loc = Expr.to_loc expr in
        let* heap_elem_type_qual_iden = Rewriter.ProgUtils.get_au_utils_rep_type loc call_qual_ident 
            
        in

        let heap_elem_type = Type.mk_var loc heap_elem_type_qual_iden in
  
        let call_name = call_qual_ident in
        let au_heap_name = au_heap_name call_name in
        let au_heap_qual_ident = QualIdent.from_ident au_heap_name in
        let au_heap_expr = Expr.mk_var ~typ:(Type.mk_map loc Type.ref heap_elem_type) au_heap_qual_ident in
  
        let au_heap2_name = au_heap_name2 call_name in
        let au_heap2_qual_ident = QualIdent.from_ident au_heap2_name in
        let au_heap2_expr = Expr.mk_var ~typ:(Type.mk_map loc Type.ref heap_elem_type) au_heap2_qual_ident in
  
        let* (au_heapchunk_operator: qual_ident) = 
          Rewriter.ProgUtils.get_au_utils_comp loc call_name
        in

        let* (au_heap_valid_fn: qual_ident) = 
          Rewriter.ProgUtils.get_au_utils_valid loc call_name
        in

        let* au_ra_uncommitted_constr = Rewriter.ProgUtils.au_ra_uncommitted_constr_qual_ident loc call_qual_ident in
        let* au_ra_committed_constr = Rewriter.ProgUtils.au_ra_committed_constr_qual_ident loc call_qual_ident in

        let havoc_stmt = Stmt.mk_havoc ~loc au_heap2_qual_ident in
        let assume_stmt = 
          let new_token_var = { Type.var_name = Ident.fresh loc "tok"; var_loc = loc; 
          var_type = Type.atomic_token; var_const = false; var_ghost = false; var_implicit = false; } in

          let new_token_expr = Expr.from_var_decl new_token_var in

          let token_var_eq_given_token = Expr.mk_eq new_token_expr token in
          
          let new_chunk = 
            (match expr with
            | App (AUPred _, _ :: args, _) -> 
              
              Expr.mk_app ~loc ~typ:heap_elem_type (Expr.DataConstr au_ra_uncommitted_constr) [Expr.mk_tuple args]

            | App (AUPredCommit _, _ :: args, _) -> 
              let ret_val = List.last_exn args in
              let call_args = List.drop_last_exn args
              
              in
              
              Expr.mk_app ~loc ~typ:heap_elem_type (Expr.DataConstr au_ra_committed_constr) [Expr.mk_tuple call_args; ret_val]

            | _ -> Error.error loc "Internal error"
            )
          in
          
          Stmt.mk_assume_expr ~loc 
          ~cmnt:(Some ((match cmnt with | None -> "" | Some cmnt -> cmnt) ^  "\ninhale: " ^ (Stdlib.Format.asprintf "%a" Expr.pr (Expr.mk_binder Forall univ_vars_list (Expr.mk_impl (Expr.mk_and conds) expr)))))

          (Expr.mk_binder ~trigs:[[Expr.mk_maplookup ~loc au_heap2_expr new_token_expr]; [Expr.mk_maplookup ~loc au_heap_expr new_token_expr]]
          
          ~loc ~typ:Type.bool Forall [new_token_var] 
            (Expr.mk_binder ~loc ~typ:Type.bool Forall univ_vars_list
              (Expr.mk_app ~loc ~typ:Type.bool Expr.Ite [

                (* m1(a,b,c) && l == f1(a, b, c) *)
                Expr.mk_and ~loc (token_var_eq_given_token :: conds);

                (* au$Heap2[l] == field.comp( field$Heap[l], f2(a, b, c) ) *)
                Expr.mk_eq ~loc (Expr.mk_maplookup ~loc au_heap2_expr new_token_expr)
                  (Expr.mk_app ~loc ~typ:heap_elem_type 
                    (Expr.Var au_heapchunk_operator)  [
                      Expr.mk_maplookup ~loc au_heap_expr new_token_expr;
                      new_chunk;
                    ] );

            
                (* au$Heap2[l] == au$Heap[l] *)
                Expr.mk_eq ~loc (Expr.mk_maplookup ~loc au_heap2_expr new_token_expr) 
                  (Expr.mk_maplookup ~loc au_heap_expr new_token_expr);
              ])
            )
          )
        in

        (* au$Heap := au$Heap2 *)
        let eq_stmt = Stmt.mk_assign ~loc [au_heap_expr] au_heap2_expr in
        
        (* let* au_valid_fn = Rewriter.ProgUtils.get_au_utils_valid (Expr.to_loc expr) (Expr.to_qual_ident e2) in
        let heap_valid_stmt = Stmt.mk_assert_expr ~loc 
          (Expr.mk_app ~loc ~typ:Type.bool (Expr.Var au_valid_fn) [au_heap_expr])

        in *)

        let assume_heap_valid = Stmt.mk_assume_expr ~loc 
          (Expr.mk_app ~loc ~typ:Type.bool (Expr.Var au_heap_valid_fn) [au_heap_expr]) 
        
        in

        let* injectivity_assertion = generate_injectivity_assertions universal_quants conds token in

        let stmts_list = match univ_quants_list with
        | [] -> []
        | _ -> [injectivity_assertion]

        in

        let stmts_list = stmts_list @ [havoc_stmt; assume_stmt; eq_stmt; assume_heap_valid] in

        let stmt = Stmt.mk_block_stmt ~loc stmts_list in

        Rewriter.return stmt


      | e ->
        let* is_e_pure = Rewriter.ProgUtils.is_expr_pure e in
        if is_e_pure then
          let body_expr = match conds with
          | [] -> e
          | _ -> Expr.mk_impl (Expr.mk_and conds) e 
        in
          let assume_expr = Expr.mk_binder ~loc:(Expr.to_loc e) ~typ:Type.bool ~trigs:(universal_quants.triggers) Forall (List.map univ_quants_list ~f:(fun (_, v_d) -> v_d)) body_expr in
          Rewriter.return (Stmt.mk_assume_expr ~loc:(Expr.to_loc e) ~cmnt:(Some ((match cmnt with | None -> "" | Some cmnt -> cmnt) ^  "\ninhale: " ^ (Stdlib.Format.asprintf "%a" Expr.pr (Expr.mk_binder Forall univ_vars_list (Expr.mk_impl (Expr.mk_and conds) expr))))) assume_expr)
        else
          match e with
          | App (Var qual_ident, args, _) ->
            let* symbol = Rewriter.find_and_reify (Expr.to_loc e) qual_ident in
            begin match symbol with
            | CallDef c when Poly.(c.call_decl.call_decl_kind = Pred || c.call_decl.call_decl_kind = Invariant) ->

              let* heap_elem_type_qual_iden = Rewriter.ProgUtils.get_pred_utils_rep_type (Expr.to_loc e) qual_ident 
            
              in

              let heap_elem_type = Type.mk_var (Expr.to_loc e) heap_elem_type_qual_iden in
        
              let pred_name = qual_ident in
              let pred_heap_name = pred_heap_name pred_name in
              let pred_heap_qual_ident = QualIdent.from_ident pred_heap_name in
              let pred_heap_expr = Expr.mk_var ~typ:(Type.mk_map (Expr.to_loc e) Type.ref heap_elem_type) pred_heap_qual_ident in
        
              let pred_heap2_name = pred_heap_name2 pred_name in
              let pred_heap2_qual_ident = QualIdent.from_ident pred_heap2_name in
              let pred_heap2_expr = Expr.mk_var ~typ:(Type.mk_map (Expr.to_loc e) Type.ref heap_elem_type) pred_heap2_qual_ident in
        
              let* (pred_heapchunk_operator: qual_ident) = 
                Rewriter.ProgUtils.get_pred_utils_comp (Expr.to_loc e) pred_name
              in

              let* (pred_heap_valid_fn: qual_ident) = 
                Rewriter.ProgUtils.get_pred_utils_valid (Expr.to_loc e) pred_name
              in

              let* pred_in_types = Rewriter.ProgUtils.pred_in_types qual_ident in

              let* pred_out_types = Rewriter.ProgUtils.pred_out_types qual_ident in

              let* pred_ra_constr = Rewriter.ProgUtils.pred_ra_constr_qual_ident (Expr.to_loc e) qual_ident in

              let havoc_stmt = Stmt.mk_havoc ~loc pred_heap2_qual_ident in
              let assume_stmt = 
                let in_vars = List.map pred_in_types ~f:(fun tp -> 
                  Type.{ var_name = Ident.fresh (Expr.to_loc e) "in"; var_loc = Expr.to_loc e; 
                  var_type = tp; var_const = false; var_ghost = false; var_implicit = false; }
                ) in

                let in_vars_exprs = List.map in_vars ~f:(fun v -> Expr.from_var_decl v) in
                let in_vars_tuple = Expr.mk_tuple in_vars_exprs in
                
                
                (* let l_var = Type.{ var_name = Ident.fresh (Expr.to_loc expr) "l"; var_loc = Expr.to_loc expr; 
                var_type = Type.ref; var_const = false; var_ghost = false; var_implicit = false; } in *)

                (* let l_expr = Expr.mk_var ~typ:l_var.var_type (QualIdent.from_ident l_var.var_name) in *)

                let in_vars_eq_args = 
                  List.map2_exn in_vars (List.take args (List.length pred_in_types)) ~f:(fun var_decl arg -> 
                    Expr.mk_eq (Expr.from_var_decl var_decl) arg
                  )
                  
                in
                
                let new_chunk = 
                  let new_chunk_expr_list = match c.call_decl.call_decl_kind with 
                  | Pred -> [Expr.mk_int 1; Expr.mk_tuple (List.drop args (List.length pred_in_types))]
                  | Invariant -> [Expr.mk_tuple (List.drop args (List.length pred_in_types))]
                  | _ -> Error.error (Expr.to_loc e) "Internal error: Expected a predicate or invariant"

                  in
                  
                  Expr.mk_app ~loc ~typ:heap_elem_type (Expr.DataConstr pred_ra_constr) new_chunk_expr_list 
                in
                
                Stmt.mk_assume_expr ~loc 
                ~cmnt:(Some ((match cmnt with | None -> "" | Some cmnt -> cmnt) ^  "\ninhale: " ^ (Stdlib.Format.asprintf "%a" Expr.pr (Expr.mk_binder Forall univ_vars_list (Expr.mk_impl (Expr.mk_and conds) expr)))))

                (Expr.mk_binder ~trigs:[[Expr.mk_maplookup ~loc pred_heap2_expr in_vars_tuple]; [Expr.mk_maplookup ~loc pred_heap_expr in_vars_tuple]]
                
                ~loc ~typ:Type.bool Forall in_vars 
                  (Expr.mk_binder ~loc ~typ:Type.bool Forall univ_vars_list
                    (Expr.mk_app ~loc ~typ:Type.bool Expr.Ite [

                      (* m1(a,b,c) && l == f1(a, b, c) *)
                      Expr.mk_and ~loc (in_vars_eq_args @ conds);

                      (* pred$Heap2[l] == field.comp( field$Heap[l], f2(a, b, c) ) *)
                      Expr.mk_eq ~loc (Expr.mk_maplookup ~loc pred_heap2_expr in_vars_tuple)
                        (Expr.mk_app ~loc ~typ:heap_elem_type 
                          (Expr.Var pred_heapchunk_operator)  [
                            Expr.mk_maplookup ~loc pred_heap_expr in_vars_tuple;
                            new_chunk;
                          ] );

                  
                      (* pred$Heap2[l] == pred$Heap[l] *)
                      Expr.mk_eq ~loc (Expr.mk_maplookup ~loc pred_heap2_expr in_vars_tuple) 
                        (Expr.mk_maplookup ~loc pred_heap_expr in_vars_tuple);
                    ])
                  )
                )
              in

              (* pred$Heap := pred$Heap2 *)
              let eq_stmt = Stmt.mk_assign ~loc [pred_heap_expr] pred_heap2_expr in
              
              (* let* pred_valid_fn = Rewriter.ProgUtils.get_pred_utils_valid (Expr.to_loc expr) (Expr.to_qual_ident e2) in
              let heap_valid_stmt = Stmt.mk_assert_expr ~loc 
                (Expr.mk_app ~loc ~typ:Type.bool (Expr.Var pred_valid_fn) [pred_heap_expr])

              in *)

              let assume_heap_valid = Stmt.mk_assume_expr ~loc 
                (Expr.mk_app ~loc ~typ:Type.bool (Expr.Var pred_heap_valid_fn) [pred_heap_expr]) 
              
              in

              let* injectivity_assertion = generate_injectivity_assertions universal_quants conds (Expr.mk_tuple (List.take args (List.length pred_in_types))) in

              let stmts_list = match univ_quants_list with
              | [] -> []
              | _ -> [injectivity_assertion]

              in

              let stmts_list = stmts_list @ [havoc_stmt; assume_stmt; eq_stmt; assume_heap_valid] in

              let stmt = Stmt.mk_block_stmt ~loc stmts_list in

              Rewriter.return stmt
            | _ -> 
              Error.error (Expr.to_loc e) "Expected a predicate definition"
            end
          | _ ->
          unsupported_expr_error expr


    let rec trnsl_assume_expr ?cmnt ~loc (expr: expr) : Stmt.t Rewriter.t =
      trnsl_assume_a ?cmnt ~loc [] expr
      

    and trnsl_assume_a ?cmnt ~loc (conds: conditions) (expr: expr): Stmt.t Rewriter.t =
      let open Rewriter.Syntax in
  
      match expr with
      | App (Ite, [c; e1; e2], _) ->
        let* stmt1 = trnsl_assume_a ?cmnt ~loc (c :: conds) e1 in
  
        let not_c = Expr.mk_not ~loc:(Expr.to_loc c) c in
        let* stmt2 = trnsl_assume_a ?cmnt ~loc (not_c :: conds) e2 in
        
        Rewriter.return (Stmt.mk_block_stmt ~loc [stmt1; stmt2])
      | App (Impl, [c; e2], _) ->
        trnsl_assume_a ?cmnt ~loc (c :: conds) e2
  
      | App (And, e_list, _) ->
        let* stmts_list = Rewriter.List.map e_list ~f:(fun e -> trnsl_assume_a ?cmnt ~loc conds e) in
        
        Rewriter.return (Stmt.mk_block_stmt ~loc stmts_list)
        
  
      | _ -> trnsl_assume_a2 ?cmnt ~loc {univ_vars = []; triggers = []} conds expr

    and trnsl_assume_a2 ?cmnt ~loc (universal_quants: universal_quants) (conds: conditions) (expr: expr): Stmt.t Rewriter.t =
      let open Rewriter.Syntax in
  
      match expr with
      | App (And, e_list, _) ->
        let* stmts_list = Rewriter.List.map e_list ~f:(fun e -> trnsl_assume_a2 ?cmnt ~loc universal_quants conds e) in
  
        Rewriter.return (Stmt.mk_block_stmt ~loc stmts_list)
  
      | Binder (Forall, var_decls, trgs, e, _) ->
        let universal_quants = 
          let new_quants = List.map var_decls ~f:(fun var_decl -> (var_decl.var_name, var_decl)) in
          {  
            univ_vars = universal_quants.univ_vars @ new_quants;
            triggers = match universal_quants.triggers with
            | [] -> trgs
            | _ -> List.concat_map universal_quants.triggers ~f:(fun trigs -> List.map trgs ~f:(fun trg -> trigs @ trg));
          }  
        in
          
          (* List.fold var_decls ~init:universal_quants ~f:(fun map var_decl -> 
          Map.add_exn map ~key:var_decl.var_name ~data:var_decl
        ) in *)
        let* stmt = trnsl_assume_a2 ?cmnt ~loc universal_quants conds e in
  
        Rewriter.return stmt
  
      | _ -> trnsl_assume_a2' ?cmnt ~loc universal_quants conds expr


    and trnsl_assume_a2' ?cmnt ~loc (universal_quants: universal_quants) (conds: conditions) (expr: expr): Stmt.t Rewriter.t =
      let open Rewriter.Syntax in
  
      match expr with
      | App (And, e_list, _) ->
        let* stmts_list = Rewriter.List.map e_list ~f:(fun e -> trnsl_assume_a2' ?cmnt ~loc universal_quants conds e) in

        Rewriter.return (Stmt.mk_block_stmt ~loc stmts_list)
        
      | App (Impl, [c; e2], _) ->
        trnsl_assume_a2' ?cmnt ~loc universal_quants (c :: conds) e2
      
      | App (Ite, [c; e1; e2], _) ->
        let* stmt1 = trnsl_assume_a2' ?cmnt ~loc universal_quants (c :: conds) e1 in
  
        let not_c = Expr.mk_not ~loc:(Expr.to_loc c) c in
        let* stmt2 = trnsl_assume_a2' ?cmnt ~loc universal_quants (not_c :: conds) e2 in
        
        Rewriter.return (Stmt.mk_block_stmt ~loc [stmt1; stmt2])
  
      | _ -> trnsl_assume_a0 ?cmnt ~loc universal_quants conds expr


      and trnsl_assume_a0 ?cmnt ~loc (universal_quants: universal_quants) (conds: conditions) (expr: expr): Stmt.t Rewriter.t =
        let open Rewriter.Syntax in
  
        let univ_quants_list = universal_quants.univ_vars in
        let univ_vars_list = List.map univ_quants_list ~f:(fun (var, var_decl) -> var_decl) in
  
        match expr with
        | App (And, e_list, _) ->
          let* stmts_list = Rewriter.List.map e_list ~f:(fun e -> trnsl_assume_a0 ?cmnt ~loc universal_quants conds e) in
            
          Rewriter.return (Stmt.mk_block_stmt ~loc stmts_list)
  
    
        | App (Own, [e1; e2; e3], _) -> begin    
          (* forall a, b, c :: m1(a, b, c) ==> own(f1(a, b, c), field, f2(a, b, c))
    
          ===>
    
          // asserting injectivity of functions
          assert forall a, b, c, a', b', c' :: m1(a, b, c) && m1(a', b', c') ==> f1(a, b, c) == f1(a', b', c') ==> (a == a' && b == b' && c == c')
    
          havoc(field$Heap2);
    
          assert forall l: Ref :: 
            forall a, b, c :: m1(a,b,c) && l == f1(a, b, c) ?
                field$Heap2[l] == field.comp( field$Heap[l], f2(a, b, c) ) :
              field$Heap2[l] == field$Heap[l]
    
          field$Heap := field$Heap2
          assume field.valid(field$Heap)
          
          *)
  
          let field_type = match Expr.to_type e2 with
            | App (Fld, [tp_expr], _) -> tp_expr
            | _ -> Error.type_error (Expr.to_loc e2) "Expected field identifier."
          in
    
          let field_name = (Expr.to_qual_ident e2) in
          let field_heap_name = field_heap_name field_name in
          let field_heap_qual_ident = QualIdent.from_ident field_heap_name in
          let field_heap_expr = Expr.mk_var ~typ:(Type.mk_map (Expr.to_loc e2) Type.ref field_type) field_heap_qual_ident in
  
          let* (field_heapchunk_operator: qual_ident) = 
            Rewriter.ProgUtils.get_field_utils_heapchunk_compare (Expr.to_loc e2) field_name
          in
  
          let* (field_heap_valid_fn: qual_ident) = 
            Rewriter.ProgUtils.get_field_utils_valid (Expr.to_loc e2) field_name
          in
  
          let assume_stmt = 
            Stmt.mk_assume_expr ~loc ~cmnt:(Some ((match cmnt with | None -> "" | Some cmnt -> (cmnt ^ "\n")) ^  "assume: " ^ (Stdlib.Format.asprintf "%a" Expr.pr (Expr.mk_binder Forall univ_vars_list (Expr.mk_impl (Expr.mk_and conds) expr)))))

              (Expr.mk_binder ~loc ~typ:Type.bool Forall univ_vars_list
                (Expr.mk_impl ~loc 
                  (Expr.mk_and ~loc conds)

                  (Expr.mk_app ~loc ~typ:Type.bool 
                    (Expr.Var field_heapchunk_operator) [
                    Expr.mk_maplookup ~loc field_heap_expr e1;
                    e3;
                    ]
                  )
                )
              )
  
          in
  
          Rewriter.return assume_stmt
        end
  
        | App (AUPred call_qual_ident, token :: args, _) | App (AUPredCommit call_qual_ident, token :: args, _) ->
          Logs.debug (fun m -> m "Rewrites.HeapsExplicitTrnsl.Trnslassume.trnsl_assume_a0: expr: %a" Expr.pr expr);
          let loc = Expr.to_loc expr in
          let* heap_elem_type_qual_iden = Rewriter.ProgUtils.get_au_utils_rep_type loc call_qual_ident 
              
          in
  
          let heap_elem_type = Type.mk_var loc heap_elem_type_qual_iden in
    
          let call_name = call_qual_ident in
          let au_heap_name = au_heap_name call_name in
          let au_heap_qual_ident = QualIdent.from_ident au_heap_name in
          let au_heap_expr = Expr.mk_var ~typ:(Type.mk_map loc Type.ref heap_elem_type) au_heap_qual_ident in
    
          let* (au_heapchunk_operator: qual_ident) = 
            Rewriter.ProgUtils.get_au_utils_heapchunk_compare loc call_name
          in
  
          let* au_ra_uncommitted_constr = Rewriter.ProgUtils.au_ra_uncommitted_constr_qual_ident loc call_qual_ident in
          let* au_ra_committed_constr = Rewriter.ProgUtils.au_ra_committed_constr_qual_ident loc call_qual_ident in
  
          let assume_stmt = 
            let new_chunk = 
              (match expr with
              | App (AUPred _, _ :: args, _) -> 
                
                Expr.mk_app ~loc ~typ:heap_elem_type (Expr.DataConstr au_ra_uncommitted_constr) [Expr.mk_tuple args]
  
              | App (AUPredCommit _, _ :: args, _) -> 
                let ret_val = List.last_exn args in
                let call_args = List.drop_last_exn args
                
                in
                
                Expr.mk_app ~loc ~typ:heap_elem_type (Expr.DataConstr au_ra_committed_constr) [Expr.mk_tuple call_args; ret_val]
  
              | _ -> Error.error loc "Internal error"
              )
            in
            
            Stmt.mk_assume_expr ~loc 
            ~cmnt:(Some ((match cmnt with | None -> "" | Some cmnt -> cmnt) ^  "\nassume: " ^ (Stdlib.Format.asprintf "%a" Expr.pr (Expr.mk_binder Forall univ_vars_list (Expr.mk_impl (Expr.mk_and conds) expr)))))
  
              (Expr.mk_binder ~loc ~typ:Type.bool Forall univ_vars_list
                (Expr.mk_impl ~loc 
                  (Expr.mk_and ~loc conds)
  
                  (Expr.mk_app ~loc ~typ:Type.bool 
                    (Expr.Var au_heapchunk_operator)  [
                      Expr.mk_maplookup ~loc au_heap_expr token;
                      new_chunk;
                    ] 
                  )
                )
              )
          in
  
          Rewriter.return assume_stmt
  
  
        | e ->
          let* is_e_pure = Rewriter.ProgUtils.is_expr_pure e in
          if is_e_pure then
            let body_expr = match conds with
            | [] -> e
            | _ -> Expr.mk_impl (Expr.mk_and conds) e 
          in
            let assume_expr = Expr.mk_binder ~loc:(Expr.to_loc e) ~typ:Type.bool ~trigs:(universal_quants.triggers) Forall (List.map univ_quants_list ~f:(fun (_, v_d) -> v_d)) body_expr in
            Rewriter.return (Stmt.mk_assume_expr ~loc:(Expr.to_loc e) ~cmnt:(Some ((match cmnt with | None -> "" | Some cmnt -> cmnt) ^  "\nassume: " ^ (Stdlib.Format.asprintf "%a" Expr.pr (Expr.mk_binder Forall univ_vars_list (Expr.mk_impl (Expr.mk_and conds) expr))))) assume_expr)
          else
            match e with
            | App (Var qual_ident, args, _) ->
              let* symbol = Rewriter.find_and_reify (Expr.to_loc e) qual_ident in
              begin match symbol with
              | CallDef c when Poly.(c.call_decl.call_decl_kind = Pred || c.call_decl.call_decl_kind = Invariant) ->
  
                let* heap_elem_type_qual_iden = Rewriter.ProgUtils.get_pred_utils_rep_type (Expr.to_loc e) qual_ident 
              
                in
  
                let heap_elem_type = Type.mk_var (Expr.to_loc e) heap_elem_type_qual_iden in
          
                let pred_name = qual_ident in
                let pred_heap_name = pred_heap_name pred_name in
                let pred_heap_qual_ident = QualIdent.from_ident pred_heap_name in
                let pred_heap_expr = Expr.mk_var ~typ:(Type.mk_map (Expr.to_loc e) Type.ref heap_elem_type) pred_heap_qual_ident in
          
                let* (pred_heapchunk_operator: qual_ident) = 
                  Rewriter.ProgUtils.get_pred_utils_heapchunk_compare (Expr.to_loc e) pred_name
                in
  
                let* pred_in_types = Rewriter.ProgUtils.pred_in_types qual_ident in
  
                let* pred_out_types = Rewriter.ProgUtils.pred_out_types qual_ident in
  
                let* pred_ra_constr = Rewriter.ProgUtils.pred_ra_constr_qual_ident (Expr.to_loc e) qual_ident in
  
                let assume_stmt =                   
                  (* let l_var = Type.{ var_name = Ident.fresh (Expr.to_loc expr) "l"; var_loc = Expr.to_loc expr; 
                  var_type = Type.ref; var_const = false; var_ghost = false; var_implicit = false; } in *)
  
                  (* let l_expr = Expr.mk_var ~typ:l_var.var_type (QualIdent.from_ident l_var.var_name) in *)
                  
                  let new_chunk = 
                    let new_chunk_expr_list = match c.call_decl.call_decl_kind with 
                    | Pred -> [Expr.mk_int 1; Expr.mk_tuple (List.drop args (List.length pred_in_types))]
                    | Invariant -> [Expr.mk_tuple (List.drop args (List.length pred_in_types))]
                    | _ -> Error.error (Expr.to_loc e) "Internal error: Expected a predicate or invariant"
  
                    in
                    
                    Expr.mk_app ~loc ~typ:heap_elem_type (Expr.DataConstr pred_ra_constr) new_chunk_expr_list 
                  in
                  
                  Stmt.mk_assume_expr ~loc 
                  ~cmnt:(Some ((match cmnt with | None -> "" | Some cmnt -> cmnt) ^  "\nassume: " ^ (Stdlib.Format.asprintf "%a" Expr.pr (Expr.mk_binder Forall univ_vars_list (Expr.mk_impl (Expr.mk_and conds) expr)))))
  
                  (Expr.mk_binder ~loc ~typ:Type.bool Forall univ_vars_list
                    (Expr.mk_impl ~loc 

                      (* m1(a,b,c) && l == f1(a, b, c) *)
                      (Expr.mk_and ~loc conds)

                      (* pred$Heap2[l] == field.comp( field$Heap[l], f2(a, b, c) ) *)
                      (Expr.mk_app ~loc ~typ:Type.bool 
                        (Expr.Var pred_heapchunk_operator)  [
                          Expr.mk_maplookup ~loc pred_heap_expr (Expr.mk_tuple (List.take args (List.length pred_in_types)));
                          new_chunk;
                        ] 
                      );
                    )
                  )
                in
  
                Rewriter.return assume_stmt
              | _ -> 
                Error.error (Expr.to_loc e) "Expected a predicate definition"
              end
            | _ ->
            unsupported_expr_error expr
  end

  module TrnslExhale = struct
    let rec rewriter_user_annot_elim_exists_from_exhales (stmt: Stmt.t) : (Stmt.t, expr option) Rewriter.t_ext =
      let open Rewriter.Syntax in

      let rec find_existentials (expr: expr) : var_decl list =
        match expr with
        | Binder (Exists, var_decls, trgs, e, _) -> var_decls @ find_existentials e
        | Binder (_, var_decls, trgs, e, _) -> find_existentials e
        | App (_, exprs, _) -> List.concat_map exprs ~f:find_existentials

      in

      let subst_existentials (expr: expr) (subst_map : expr qual_ident_map): expr = 
        let rec elim_exists (expr: expr) (subst_map) : expr = 
          match expr with
          | Binder (Exists, var_decls, trgs, e, _) ->
            let all_existentials_exist = List.for_all var_decls ~f:(fun var_decl -> 
              Map.mem subst_map (QualIdent.from_ident var_decl.var_name)
            ) in

            if not all_existentials_exist then
              Error.internal_error (Expr.to_loc expr) "Expected all existentials to be matched up"
            else
              e

          | Binder (b, var_decls, trgs, e, expr_attr) ->
              let e = elim_exists e subst_map in
              Binder (b, var_decls, trgs, e, expr_attr)

          | App (constr, exprs, expr_attr) ->
            let exprs = List.map exprs ~f:(fun e -> elim_exists e subst_map) in
            App (constr, exprs, expr_attr)

        in

        let expr = Expr.alpha_renaming expr subst_map in
        elim_exists expr subst_map

      in

      match stmt.stmt_desc with
      | Basic (Spec (Exhale, spec)) ->
        let* prev_expr = Rewriter.current_user_state in
        let* () = Rewriter.set_user_state None in


        Logs.debug (fun m -> m "Rewrites.HeapsExplicitTrnsl.TrnslExhale.rewriter_user_annot_elim_exists_from_exhales: prev_expr: %a; exhale_expr: %a" (Util.Print.pr_option Expr.pr) prev_expr Expr.pr spec.spec_form);
        
        let exhale_expr = spec.spec_form in
        begin
          match prev_expr with
          | None -> 
            Rewriter.return stmt
          
          | Some prev_expr ->
            Logs.debug (fun m -> m "Rewrites.HeapsExplicitTrnsl.TrnslExhale.rewriter_user_annot_elim_exists_from_exhales: prev_expr: %a; exhale_expr: %a" Expr.pr prev_expr Expr.pr exhale_expr);
            let existential_vars = find_existentials exhale_expr in 
            
              match match_up_expr spec.spec_form prev_expr existential_vars with
              | None -> 
                Rewriter.return stmt

              | Some var_map ->
                let subst_map = Map.map var_map ~f:(fun (var_decl, expr) -> expr) in
                let subst_map = (Map.map_keys_exn (module QualIdent)) subst_map ~f:(fun ident -> QualIdent.from_ident ident) in
                let spec_form = subst_existentials exhale_expr subst_map in

                let spec = { spec with spec_form } in

                Rewriter.return {stmt with stmt_desc = Basic (Spec (Exhale, spec))}
        end

      | Basic (Spec (Assert, spec)) ->
        let* () = Rewriter.set_user_state (Some spec.spec_form) in
        Rewriter.return stmt

      | Basic _ ->
        let* () = Rewriter.set_user_state None in
        Rewriter.return stmt

      | _ -> 
        (* let* () = Rewriter.set_user_state None in *)
        Rewriter.Stmt.descend stmt ~f:rewriter_user_annot_elim_exists_from_exhales
    



    

    module WitnessComputation = struct
      let rec find_witnesses_elim_exists (expr: expr) : expr Rewriter.t =
        elim_a {univ_vars = []; triggers = []} [] expr

      and elim_a (universal_quants: universal_quants) (conds: conditions) (expr: expr): expr Rewriter.t =
        let open Rewriter.Syntax in

        match expr with
        | App (Ite, [c; e1; e2], expr_attr) ->
          let* e1 = elim_a universal_quants (c :: conds) e1 in
    
          let not_c = Expr.mk_not ~loc:(Expr.to_loc c) c in
          let* e2 = elim_a universal_quants (not_c :: conds) e2 in
          
          Rewriter.return (Expr.App (Ite, [c; e1; e2], expr_attr))
        | App (Impl, [c; e2], expr_attr) ->
          let+ e2 = elim_a universal_quants (c :: conds) e2 in
          Expr.App (Impl, [c; e2], expr_attr)
    
        | App (And, e_list, expr_attr) ->
          let* e_list = Rewriter.List.map e_list ~f:(fun e -> elim_a universal_quants conds e) in

          Rewriter.return (Expr.App (And, e_list, expr_attr))

        | Binder (Forall, var_decls, trgs, e, expr_attr) ->
          let universal_quants = 
            let new_quants = List.map var_decls ~f:(fun var_decl -> (var_decl.var_name, var_decl)) in
            {  
              univ_vars = universal_quants.univ_vars @ new_quants;
              triggers = match universal_quants.triggers with
              | [] -> trgs
              | _ -> List.concat_map universal_quants.triggers ~f:(fun trigs -> List.map trgs ~f:(fun trg -> trigs @ trg));
            }  
          in

          let* e = elim_a universal_quants conds e in
    
          Rewriter.return (Expr.Binder (Forall, var_decls, trgs, e, expr_attr))
          
    
        | _ -> elim_a1 universal_quants conds expr
  

      and elim_a1 (univ_vars: universal_quants) (univ_conds: conditions) (expr: expr): expr Rewriter.t = 
        let open Rewriter.Syntax in

        match expr with
        | Binder (Exists, var_decls, trgs, e, expr_attr) ->
          let init_map = List.fold var_decls ~init:(Map.empty (module Ident)) ~f:(fun map var_decl -> 
            Map.add_exn map ~key:var_decl.var_name ~data:[]
          ) in
          let* witnesses = elim_a0 univ_vars var_decls (univ_conds, []) e init_map in

          Logs.debug (fun m -> m "Rewrites.HeapsExplicitTrnsl.WitnessComputation.elim_a1: witnesses:");

          List.iter (Map.to_alist witnesses) ~f:(fun (id, witns) ->
            List.iter witns ~f:(fun (conds, e) ->
                Logs.debug (fun m -> m "id: %a, conds: %a, e: %a" Ident.pr id (Fmt.Dump.list Expr.pr) conds (Fmt.Dump.option Expr.pr) e)
            )
          );

          let* skolemized_exprs = Rewriter.List.map var_decls ~f:(fun var_decl ->
              let* postconds, optn_args = (match Map.find witnesses var_decl.var_name with
                | None -> Rewriter.return ([], [])
                | Some witness_list -> 
                  let witness_list = List.filter witness_list ~f:(fun (conds, e) -> Option.is_some e) in

                  let postconds, optn_args =
                  List.unzip
                  (List.map witness_list ~f:(fun (conds, e) -> 
                    let witness = (Option.value_exn e) in
                    let optn_arg = { 
                      Type.var_name = Ident.fresh var_decl.var_loc ("witness_" ^ (Ident.to_string var_decl.var_name));
                      var_loc = var_decl.var_loc;
                      var_type = (Expr.to_type witness);
                      var_const = true;
                      var_ghost = false;
                      var_implicit = false;
                    } in

                    Expr.mk_impl 
                      (Expr.mk_and (univ_conds @ conds)) 
                      (Expr.mk_eq 
                        (Expr.from_var_decl var_decl) 
                        (Expr.from_var_decl optn_arg)
                      ), (optn_arg, witness)
                  ))

                  in

                  let conds = List.concat_map witness_list ~f:(fun (conds, _) -> conds) in
                  let conds = univ_conds @ conds in

                  let symbols = List.fold conds ~init:(Set.empty (module QualIdent)) ~f:(fun symbols cond -> 
                    Expr.symbols cond
                  ) in

                  let locals = Set.filter symbols ~f:(fun s -> (QualIdent.is_local s) && not (List.exists univ_vars.univ_vars ~f:(fun (i, _) -> Ident.(i = (QualIdent.unqualify s))))) in

                  let locals = Set.to_list locals in

                  let* locals_var_decls = Rewriter.List.map locals ~f:(fun qual_ident -> 
                    let+ symbol = Rewriter.find_and_reify var_decl.var_loc qual_ident in
                    match symbol with
                    | VarDef v -> v.var_decl
                    | _ -> Error.error var_decl.var_loc "Expected a variable declaration"
                    )
                  in

                  Logs.debug (fun m -> m "Rewrites.HeapsExplicitTrnsl.WitnessComputation.elim_a1: locals_var_decls: %a" (Fmt.Dump.list QualIdent.pr) locals);

                  let optn_args = optn_args @ (List.map locals_var_decls ~f:(fun var_decl -> (var_decl, Expr.from_var_decl var_decl))) in

                  Rewriter.return (postconds, optn_args)
              ) in

              let+ expr = generate_skolem_function univ_vars var_decl ~postconds ~optn_args ~loc:var_decl.var_loc in

              expr
          )

          in

          let renaming_map = List.fold2_exn var_decls skolemized_exprs ~init:(Map.empty (module QualIdent)) ~f:(fun map var_decl expr -> 
            Map.set map ~key:(QualIdent.from_ident var_decl.var_name) ~data:expr
          ) in

          let e = Expr.alpha_renaming e renaming_map in

          Rewriter.return e
          
          
    
        | _ -> 
          (* No existentials found *)
          Rewriter.return expr

      and elim_a0 (univ_vars: universal_quants) (exist_vars: var_decl list) (univ_conds, exist_conds: conditions * conditions) (expr: expr) (witness_map: ((conditions * expr option) list ident_map)) : ((conditions * expr option) list ident_map) Rewriter.t =
        let open Rewriter.Syntax in

        match expr with
        | App (And, e_list, _) ->
          
          let* witness_map = Rewriter.List.fold_left e_list ~init:witness_map ~f:(fun map e -> elim_a0 univ_vars exist_vars (univ_conds, exist_conds) e map) in

          Rewriter.return witness_map
        
        | App (Impl, [c; e2], _) ->
          let* witness_map = elim_a0 univ_vars exist_vars (univ_conds, c :: exist_conds) e2 witness_map in

          Rewriter.return witness_map

        | App (Ite, [c; e1; e2], _) ->
          let* witness_map = elim_a0 univ_vars exist_vars (univ_conds, c :: exist_conds) e1 witness_map in

          let not_c = Expr.mk_not ~loc:(Expr.to_loc c) c in
          let* witness_map = elim_a0 univ_vars exist_vars (univ_conds, not_c :: exist_conds) e2 witness_map in

          Rewriter.return witness_map

        | App (Own, [loc_expr; field_expr; val_expr], _) ->
          let field_name = try Expr.to_qual_ident field_expr 
            with _ -> Error.type_error (Expr.to_loc field_expr) "Expected field identifier." 
          in

          let field_elem_type = (match Expr.to_type field_expr with
            | App (Fld, [tp_expr], _) -> tp_expr
            | _ -> Error.type_error (Expr.to_loc field_expr) "Expected field identifier.")
          in

          let field_heap_name = field_heap_name field_name in
          let field_heap_type = Type.mk_map (Expr.to_loc expr) Type.ref field_elem_type in

          let concrete_expr = Expr.mk_maplookup (Expr.mk_var ~typ:field_heap_type (QualIdent.from_ident field_heap_name)) loc_expr in

          let relevant_vars = List.filter exist_vars ~f:(fun var_decl -> Set.exists (Expr.local_vars val_expr) ~f:(Ident.equal var_decl.var_name)) in

          let* witnesses = core_witness_comp relevant_vars concrete_expr val_expr false in

          Logs.debug (fun m -> m "Rewrites.HeapsExplicitTrnsl.WitnessComputation.elim_a0: witnesses: %a" (Fmt.Dump.list (fun ppf (i, e)  -> Stdlib.Format.fprintf ppf "%a -> %a" Ident.pr i Expr.pr e)) (Map.to_alist witnesses));

          let witness_map = List.fold relevant_vars ~init:witness_map ~f:(fun witness_map var_decl -> 
            let existing_val = 
              match Map.find witness_map var_decl.var_name with
              | None -> []
              | Some v -> v
            in  

            let new_val = (exist_conds, Map.find witnesses var_decl.var_name) :: existing_val in

            Map.set witness_map ~key:var_decl.var_name ~data:new_val
            
          ) in

          Rewriter.return witness_map

        | App (Var qual_ident, args, _) ->
          let* symbol = Rewriter.find_and_reify (Expr.to_loc expr) qual_ident in

          (match symbol with
          | CallDef c when Poly.(c.call_decl.call_decl_kind = Pred) ->
            let pred_heap = pred_heap_name qual_ident in
            let* pred_in_types = Rewriter.ProgUtils.pred_in_types qual_ident in
            let* pred_out_types = Rewriter.ProgUtils.pred_out_types qual_ident in

            let* pred_heap_type = Rewriter.ProgUtils.pred_heap_type qual_ident in
            let pred_heap_expr = Expr.mk_var (QualIdent.from_ident pred_heap) ~typ:pred_heap_type in


            let* pred_val_destr = Rewriter.ProgUtils.pred_ra_val_destr_qual_ident (Expr.to_loc expr) qual_ident in

            let pred_heap_val = Expr.mk_app ~typ:(Type.mk_prod (Expr.to_loc expr) pred_out_types) (DataDestr pred_val_destr) [(Expr.mk_maplookup pred_heap_expr (Expr.mk_tuple (List.take args (List.length pred_in_types))))] in

            let* pred_heap_expanded_type = Typing.ProcessTypeExpr.expand_type_expr (Expr.to_type pred_heap_val) in

            Logs.debug (fun m -> m "Rewrites.HeapsExplicitTrnsl.WitnessComputation.elim_a0: pred_heap_expanded_type: %a" Type.pr pred_heap_expanded_type);

            let pred_heap_val_expanded_typ = Expr.set_type pred_heap_val (pred_heap_expanded_type)
            
            in

            let concrete_exprs = List.mapi (List.drop args (List.length pred_in_types)) ~f:(fun i _ -> 
              Expr.mk_tuple_lookup pred_heap_val_expanded_typ i  
            ) in

            let out_args_concrete_exprs = List.zip_exn (List.drop args (List.length pred_in_types)) concrete_exprs in
            
            let* witness_map = Rewriter.List.fold_left out_args_concrete_exprs ~init:witness_map ~f:(fun map (out_arg, concrete_expr) -> 
              
              let* witnesses = core_witness_comp exist_vars concrete_expr out_arg true in 
            
              let witness_map = List.fold exist_vars ~init:witness_map ~f:(fun witness_map var_decl -> 
                let existing_val = Map.find_exn witness_map var_decl.var_name in  
    
                let new_val = (exist_conds, Map.find witnesses var_decl.var_name) :: existing_val in
    
                Map.set witness_map ~key:var_decl.var_name ~data:new_val
                
              ) in

              Rewriter.return witness_map

            ) in
            
            Rewriter.return witness_map

          | _ -> 
            Rewriter.return (Map.empty (module Ident))
        )


        | _ -> 
          Rewriter.return (Map.empty (module Ident))


      and core_witness_comp (exists: var_decl list) (concrete_expr: expr) (given_expr: expr) (exact: bool) : (expr ident_map) Rewriter.t = 
        let open Rewriter.Syntax in

        Logs.debug (fun m -> m "Rewrites.HeapsExplicitTrnsl.WitnessComputation.core_witness_comp: exists: %a, concrete_expr: %a, given_expr: %a, exact: %b" 
          (Fmt.Dump.list Ident.pr) (List.map exists ~f:(fun v -> v.var_name)) Expr.pr concrete_expr Expr.pr given_expr exact);

        match exact with
        | false ->
          let ra_name = match (Expr.to_type given_expr) with
            | App (Var ra_name, [], _) -> (QualIdent.pop ra_name)
            | App (Data (ra_name, _), [], _) -> (QualIdent.pop ra_name)
            | tp -> Error.type_error (Expr.to_loc given_expr) ("Expected an RA type; found: " ^ Type.to_string tp)
        
          in

          let* orig_name, ra_def, _ = Rewriter.find (Expr.to_loc given_expr) ra_name in

          if QualIdent.(orig_name = Predefs.lib_auth_mod_qual_ident) then
            (match given_expr with
            | App (DataConstr constr_ident, exprs, _) ->
              if Ident.(QualIdent.unqualify constr_ident = Predefs.lib_auth_frag_constr_ident) then
                let auth_chunk = Expr.mk_app ~typ:(Expr.to_type (List.hd_exn exprs)) (Expr.DataDestr (QualIdent.append ra_name Predefs.lib_auth_frag_destr1_ident)) [concrete_expr] in
                core_witness_comp exists auth_chunk (List.hd_exn exprs) true

                (* Error.error_simple "unimplemented" *)

              else
                Rewriter.return (Map.empty (module Ident))
                
            | _ -> 
              Error.type_error (Expr.to_loc given_expr) "Expected a data constructor."
            )

          else if QualIdent.(orig_name = Predefs.lib_frac_mod_qual_ident) then
            (match given_expr with
            | App (DataConstr constr_ident, exprs, _) ->
              if Ident.(QualIdent.unqualify constr_ident = Predefs.lib_frac_chunk_constr_ident) then
                let frac_chunk = Expr.mk_app ~typ:(Expr.to_type (List.hd_exn exprs)) (Expr.DataDestr (QualIdent.append ra_name Predefs.lib_frac_chunk_destr1_ident)) [concrete_expr] in
                core_witness_comp exists frac_chunk (List.hd_exn exprs) true

              else
                Rewriter.return (Map.empty (module Ident))

            | _ -> 
              Error.type_error (Expr.to_loc given_expr) "Expected a data constructor."
            )

          else if QualIdent.(orig_name = Predefs.lib_agree_mod_qual_ident) then
            (match given_expr with
            | App (DataConstr constr_ident, exprs, _) ->
              if Ident.(QualIdent.unqualify constr_ident = Predefs.lib_agree_constr_ident) then
                let agree_chunk = Expr.mk_app ~typ:(Expr.to_type (List.hd_exn exprs)) (Expr.DataDestr (QualIdent.append ra_name Predefs.lib_agree_destr1_ident)) [concrete_expr] in
                core_witness_comp exists agree_chunk (List.hd_exn exprs) true

              else
                Rewriter.return (Map.empty (module Ident))

            | _ -> 
              Error.type_error (Expr.to_loc given_expr) "Expected a data constructor."
            )

          else
            Rewriter.return (Map.empty (module Ident))
            
        
        | true ->
          match given_expr with
          | App (Var ident, [], _) ->
            if List.exists exists ~f:(fun var_decl -> Poly.((QualIdent.from_ident var_decl.var_name) = ident)) then
              Rewriter.return (Map.singleton (module Ident) (QualIdent.unqualify ident) concrete_expr)
            else
              Rewriter.return (Map.empty (module Ident))

          | App (Tuple, exprs, _) ->
            let* witness_map = Rewriter.List.fold_left exprs ~init:(Map.empty (module Ident)) ~f:(fun witness_map expr -> 
              let* new_witness_map = core_witness_comp exists concrete_expr expr true in

              let witness_map = Map.merge witness_map new_witness_map ~f:(fun ~key:_ -> function
                | `Both (w1, w2) -> Some w1
                | `Left w1 -> Some w1
                | `Right w2 -> Some w2
              ) in

              Rewriter.return witness_map
            ) in

            Rewriter.return witness_map

          | App (DataConstr qual_iden, exprs, _) ->
            let* destrs = Rewriter.ProgUtils.get_data_destrs_from_constr qual_iden in

            let* destrs = Rewriter.List.map destrs ~f:(fun destr -> 
              let+ destr_ret_type =
                let* destr_symbol = Rewriter.find_and_reify (Expr.to_loc given_expr) destr in
                match destr_symbol with
                | DestrDef destr -> Rewriter.return destr.destr_return_type
                | _ -> Error.error (Expr.to_loc given_expr) "Expected a destr definition"
              in

              destr, destr_ret_type

            ) in

            let destr_exprs = List.map2_exn destrs exprs ~f:(fun (destr, ret_typ) expr -> 
               Expr.mk_app ~typ:ret_typ (Expr.DataDestr destr) [expr]
              
            ) in

            let* witness_map = Rewriter.List.fold_left destr_exprs ~init:(Map.empty (module Ident)) ~f:(fun witness_map destr_expr -> 
              let* new_witness_map = core_witness_comp exists concrete_expr destr_expr true in

              let witness_map = Map.merge witness_map new_witness_map ~f:(fun ~key:_ -> function
                | `Both (w1, w2) -> Some w1
                | `Left w1 -> Some w1
                | `Right w2 -> Some w2
              ) in

              Rewriter.return witness_map
            ) in

            Rewriter.return witness_map

          | _ ->
            Rewriter.return (Map.empty (module Ident))
    end


    let rec rewriter_find_witness_elim_exists_from_exhale (stmt: Stmt.t) : Stmt.t Rewriter.t =
      let open Rewriter.Syntax in
      match stmt.stmt_desc with
      | Basic (Spec (Exhale, spec)) ->
        let exhale_expr = spec.spec_form in
        begin
          let* elim_expr = WitnessComputation.find_witnesses_elim_exists exhale_expr in

          let spec = { spec with spec_form = elim_expr } in

          Rewriter.return {stmt with stmt_desc = Basic (Spec (Exhale, spec))}
        end

      | Basic (Spec (Assert, spec)) ->
        let assert_expr = spec.spec_form in
        begin
          let* elim_expr = WitnessComputation.find_witnesses_elim_exists assert_expr in

          let spec = { spec with spec_form = elim_expr } in

          Rewriter.return {stmt with stmt_desc = Basic (Spec (Assert, spec))}
        end

      | _ -> 
        Rewriter.Stmt.descend stmt ~f:rewriter_find_witness_elim_exists_from_exhale
    
    let rec trnsl_exhale_expr ?cmnt ~loc (expr: expr) : Stmt.t Rewriter.t =
      trnsl_exhale_a ?cmnt ~loc [] expr
      
    and trnsl_exhale_a ?cmnt ~loc (conds: conditions) (expr: expr): Stmt.t Rewriter.t =
      let open Rewriter.Syntax in
  
      match expr with
      | App (Ite, [c; e1; e2], _) ->
        let* stmt1 = trnsl_exhale_a ?cmnt ~loc (c :: conds) e1 in
  
        let not_c = Expr.mk_not ~loc:(Expr.to_loc c) c in
        let* stmt2 = trnsl_exhale_a ?cmnt ~loc (not_c :: conds) e2 in
        
        Rewriter.return (Stmt.mk_block_stmt ~loc [stmt1; stmt2])
      | App (Impl, [c; e2], _) ->
        trnsl_exhale_a ?cmnt ~loc (c :: conds) e2
  
      | App (And, e_list, _) ->
        let* stmts_list = Rewriter.List.map e_list ~f:(fun e -> trnsl_exhale_a ?cmnt ~loc conds e) in
        
        Rewriter.return (Stmt.mk_block_stmt ~loc stmts_list)
        
      | _ -> trnsl_exhale_a2 ?cmnt ~loc {univ_vars = []; triggers = []} conds expr

    and trnsl_exhale_a2 ?cmnt ~loc (universal_quants: universal_quants) (conds: conditions) (expr: expr): Stmt.t Rewriter.t =
      let open Rewriter.Syntax in
  
      match expr with
      | App (And, e_list, _) ->
        let* stmts_list = Rewriter.List.map e_list ~f:(fun e -> trnsl_exhale_a2 ?cmnt ~loc universal_quants conds e) in
  
        Rewriter.return (Stmt.mk_block_stmt ~loc stmts_list)
  
      | Binder (Forall, var_decls, trgs, e, _) ->
        let universal_quants = 
          let new_quants = List.map var_decls ~f:(fun var_decl -> (var_decl.var_name, var_decl)) in
          {  
            univ_vars = universal_quants.univ_vars @ new_quants;
            triggers = match universal_quants.triggers with
            | [] -> trgs
            | _ -> List.concat_map universal_quants.triggers ~f:(fun trigs -> List.map trgs ~f:(fun trg -> trigs @ trg));
          }    
        in
          
          (* List.fold var_decls ~init:universal_quants ~f:(fun map var_decl -> 
          Map.add_exn map ~key:var_decl.var_name ~data:var_decl
        ) in *)
        let* stmt = trnsl_exhale_a2 ?cmnt ~loc universal_quants conds e in
  
        Rewriter.return stmt
  
      | _ -> trnsl_exhale_a2' ?cmnt ~loc universal_quants conds expr


    and trnsl_exhale_a2' ?cmnt ~loc (universal_quants: universal_quants) (conds: conditions) (expr: expr): Stmt.t Rewriter.t =
      let open Rewriter.Syntax in
  
      match expr with
      | App (And, e_list, _) ->
        let* stmts_list = Rewriter.List.map e_list ~f:(fun e -> trnsl_exhale_a2' ?cmnt ~loc universal_quants conds e) in

        Rewriter.return (Stmt.mk_block_stmt ~loc stmts_list)
        
      | App (Impl, [c; e2], _) ->
        trnsl_exhale_a2' ?cmnt ~loc universal_quants (c :: conds) e2
      
      | App (Ite, [c; e1; e2], _) ->
        let* stmt1 = trnsl_exhale_a2' ?cmnt ~loc universal_quants (c :: conds) e1 in
  
        let not_c = Expr.mk_not ~loc:(Expr.to_loc c) c in
        let* stmt2 = trnsl_exhale_a2' ?cmnt ~loc universal_quants (not_c :: conds) e2 in
        
        Rewriter.return (Stmt.mk_block_stmt ~loc [stmt1; stmt2])
  
      | _ -> trnsl_exhale_a0 ?cmnt ~loc universal_quants conds expr

    and trnsl_exhale_a0 ?cmnt ~loc (universal_quants: universal_quants) (conds: conditions) (expr: expr): Stmt.t Rewriter.t =
      let open Rewriter.Syntax in

      let univ_quants_list = universal_quants.univ_vars in
      let univ_vars_list = List.map univ_quants_list ~f:(fun (var, var_decl) -> var_decl) in

      match expr with
      | App (And, e_list, _) ->
        let* stmts_list = Rewriter.List.map e_list ~f:(fun e -> trnsl_exhale_a0 ?cmnt ~loc universal_quants conds e) in

        Rewriter.return (Stmt.mk_block_stmt ~loc stmts_list)  
  
      | App (Own, [e1; e2; e3], _) -> begin    
        (* forall a, b, c :: m1(a, b, c) ==> own(f1(a, b, c), field, f2(a, b, c))
  
        ===>
  
        // asserting injectivity of functions
        assert forall a, b, c, a', b', c' :: m1(a, b, c) && m1(a', b', c') ==> f1(a, b, c) == f1(a', b', c') ==> (a == a' && b == b' && c == c')
  
        havoc(field$Heap2);
  
        assert forall l: Ref :: 
          forall a, b, c :: m1(a,b,c) && l == f1(a, b, c) ?
              field$Heap2[l] == field.frame( field$Heap[l], f2(a, b, c) ) :
            field$Heap2[l] == field$Heap[l]
  
        field$Heap := field$Heap2
        assert field.valid(field$Heap)
        
        *)

        let field_type = match Expr.to_type e2 with
          | App (Fld, [tp_expr], _) -> tp_expr
          | _ -> Error.type_error (Expr.to_loc e2) "Expected field identifier."
        in
  
        let field_name = (Expr.to_qual_ident e2) in
        let field_heap_name = field_heap_name field_name in
        let field_heap_qual_ident = QualIdent.from_ident field_heap_name in
        let field_heap_expr = Expr.mk_var ~typ:(Type.mk_map (Expr.to_loc e2) Type.ref field_type) field_heap_qual_ident in
  
        let field_heap2_name = field_heap_name2 field_name in
        let field_heap2_qual_ident = QualIdent.from_ident field_heap2_name in
        let field_heap2_expr = Expr.mk_var ~typ:(Type.mk_map (Expr.to_loc e2) Type.ref field_type) field_heap2_qual_ident in
  
        let* (field_heapchunk_operator: qual_ident) = 
          Rewriter.ProgUtils.get_field_utils_frame (Expr.to_loc e2) field_name
        in

        let* (field_heap_valid_fn: qual_ident) = 
          Rewriter.ProgUtils.get_field_utils_valid (Expr.to_loc e2) field_name
        in

        let havoc_stmt = Stmt.mk_havoc ~loc field_heap2_qual_ident in
        let assume_stmt = 
          let l_var = Type.{ var_name = Ident.fresh (Expr.to_loc expr) "l"; var_loc = Expr.to_loc expr; 
          var_type = Type.ref; var_const = false; var_ghost = false; var_implicit = false; } in

          let l_expr = Expr.mk_var ~typ:l_var.var_type (QualIdent.from_ident l_var.var_name) in
          
          let l_eq_e1_expr = (Expr.mk_eq l_expr e1) in
          
          Stmt.mk_assume_expr ~loc 
          ~cmnt:(Some ((match cmnt with | None -> "" | Some cmnt -> (cmnt ^ "\n")) ^ "exhale: " ^ (Stdlib.Format.asprintf "%a" Expr.pr (Expr.mk_binder Forall univ_vars_list (Expr.mk_impl (Expr.mk_and conds) expr)))))
          (Expr.mk_binder ~trigs:[[Expr.mk_maplookup ~loc field_heap2_expr l_expr]; [Expr.mk_maplookup ~loc field_heap_expr l_expr]]
          
          ~loc ~typ:Type.bool Forall [l_var] 
            (Expr.mk_binder ~loc ~typ:Type.bool Forall univ_vars_list
              (Expr.mk_app ~loc ~typ:Type.bool Expr.Ite [

                (* m1(a,b,c) && l == f1(a, b, c) *)
                Expr.mk_and ~loc (l_eq_e1_expr :: conds);

                (* field$Heap2[l] == field.comp( field$Heap[l], f2(a, b, c) ) *)
                Expr.mk_eq ~loc (Expr.mk_maplookup ~loc field_heap2_expr l_expr)
                  (Expr.mk_app ~loc ~typ:field_type 
                    (Expr.Var field_heapchunk_operator)  [
                      Expr.mk_maplookup ~loc field_heap_expr l_expr;
                      e3;
                    ] );

            
                (* field$Heap2[l] == field$Heap[l] *)
                Expr.mk_eq ~loc (Expr.mk_maplookup ~loc field_heap2_expr l_expr) 
                  (Expr.mk_maplookup ~loc field_heap_expr l_expr);
              ])
            )
          )
        in

        (* field$Heap := field$Heap2 *)
        let eq_stmt = Stmt.mk_assign ~loc [field_heap_expr] field_heap2_expr in
        
        (* let* field_valid_fn = Rewriter.ProgUtils.get_field_utils_valid (Expr.to_loc expr) (Expr.to_qual_ident e2) in
        let heap_valid_stmt = Stmt.mk_assert_expr ~loc 
          (Expr.mk_app ~loc ~typ:Type.bool (Expr.Var field_valid_fn) [field_heap_expr])

        in *)

        let assert_heap_valid = Stmt.mk_assert_expr ~loc 
          (Expr.mk_app ~loc ~typ:Type.bool (Expr.Var field_heap_valid_fn) [field_heap_expr]) 
        
        in

        let* injectivity_assertion = generate_injectivity_assertions universal_quants conds e1 in

        let stmts_list = match univ_quants_list with
        | [] -> []
        | _ -> [injectivity_assertion]

        in

        let stmts_list = stmts_list @ [havoc_stmt; assume_stmt; eq_stmt; assert_heap_valid] in

        let stmt = Stmt.mk_block_stmt ~loc stmts_list in

        Rewriter.return stmt
      end

      | App (AUPred call_qual_ident, token :: args, _) | App (AUPredCommit call_qual_ident, token :: args, _) ->
        let loc = Expr.to_loc expr in
        let* heap_elem_type_qual_iden = Rewriter.ProgUtils.get_au_utils_rep_type loc call_qual_ident  
            
        in

        let heap_elem_type = Type.mk_var loc heap_elem_type_qual_iden in
  
        let call_name = call_qual_ident in
        let au_heap_name = au_heap_name call_name in
        let au_heap_qual_ident = QualIdent.from_ident au_heap_name in
        let au_heap_expr = Expr.mk_var ~typ:(Type.mk_map loc Type.ref heap_elem_type) au_heap_qual_ident in
  
        let au_heap2_name = au_heap_name2 call_name in
        let au_heap2_qual_ident = QualIdent.from_ident au_heap2_name in
        let au_heap2_expr = Expr.mk_var ~typ:(Type.mk_map loc Type.ref heap_elem_type) au_heap2_qual_ident in
  
        let* (au_heapchunk_operator: qual_ident) = 
          Rewriter.ProgUtils.get_au_utils_frame loc call_name
        in

        let* (au_heap_valid_fn: qual_ident) = 
          Rewriter.ProgUtils.get_au_utils_valid loc call_name
        in

        let* au_ra_uncommitted_constr = Rewriter.ProgUtils.au_ra_uncommitted_constr_qual_ident loc call_qual_ident in
        let* au_ra_committed_constr = Rewriter.ProgUtils.au_ra_committed_constr_qual_ident loc call_qual_ident in

        let havoc_stmt = Stmt.mk_havoc ~loc au_heap2_qual_ident in
        let assume_stmt = 
          let new_token_var = { Type.var_name = Ident.fresh loc "tok"; var_loc = loc; 
          var_type = Type.atomic_token; var_const = false; var_ghost = false; var_implicit = false; } in

          let new_token_expr = Expr.from_var_decl new_token_var in

          let token_var_eq_given_token = Expr.mk_eq new_token_expr token in
            
          let new_chunk = 
            (match expr with
            | App (AUPred _, _ :: args, _) -> 
              
              Expr.mk_app ~loc ~typ:heap_elem_type (Expr.DataConstr au_ra_uncommitted_constr) [Expr.mk_tuple args]

            | App (AUPredCommit _, _ :: args, _) -> 
              let ret_val = List.last_exn args in
              let call_args = List.drop_last_exn args
              
              in
              
              Expr.mk_app ~loc ~typ:heap_elem_type (Expr.DataConstr au_ra_committed_constr) [Expr.mk_tuple call_args; ret_val]

            | _ -> Error.error loc "Internal error"
            )
          in
          
          Stmt.mk_assume_expr ~loc 
          ~cmnt:(Some ((match cmnt with | None -> "" | Some cmnt -> cmnt) ^ "\nexhale: " ^ (Stdlib.Format.asprintf "%a" Expr.pr (Expr.mk_binder Forall univ_vars_list (Expr.mk_impl (Expr.mk_and conds) expr)))))

          (Expr.mk_binder ~trigs:[[Expr.mk_maplookup ~loc au_heap2_expr new_token_expr]; [Expr.mk_maplookup ~loc au_heap_expr new_token_expr]]
          
          ~loc ~typ:Type.bool Forall [new_token_var] 
            (Expr.mk_binder ~loc ~typ:Type.bool Forall univ_vars_list
              (Expr.mk_app ~loc ~typ:Type.bool Expr.Ite [

                (* m1(a,b,c) && l == f1(a, b, c) *)
                Expr.mk_and ~loc (token_var_eq_given_token :: conds);

                (* au$Heap2[l] == field.comp( field$Heap[l], f2(a, b, c) ) *)
                Expr.mk_eq ~loc (Expr.mk_maplookup ~loc au_heap2_expr new_token_expr)
                  (Expr.mk_app ~loc ~typ:heap_elem_type 
                    (Expr.Var au_heapchunk_operator)  [
                      Expr.mk_maplookup ~loc au_heap_expr new_token_expr;
                      new_chunk;
                    ] );

            
                (* pred$Heap2[l] == pred$Heap[l] *)
                Expr.mk_eq ~loc (Expr.mk_maplookup ~loc au_heap2_expr new_token_expr) 
                  (Expr.mk_maplookup ~loc au_heap_expr new_token_expr);
              ])
            )
          )
        in

        (* pred$Heap := pred$Heap2 *)
        let eq_stmt = Stmt.mk_assign ~loc [au_heap_expr] au_heap2_expr in
        
        (* let* pred_valid_fn = Rewriter.ProgUtils.get_pred_utils_valid (Expr.to_loc expr) (Expr.to_qual_ident e2) in
        let heap_valid_stmt = Stmt.mk_assert_expr ~loc 
          (Expr.mk_app ~loc ~typ:Type.bool (Expr.Var pred_valid_fn) [pred_heap_expr])

        in *)

        let assert_heap_valid = Stmt.mk_assert_expr ~loc 
          (Expr.mk_app ~loc ~typ:Type.bool (Expr.Var au_heap_valid_fn) [au_heap_expr]) 
        
        in

        let* injectivity_assertion = generate_injectivity_assertions universal_quants conds token in

        let stmts_list = match univ_quants_list with
        | [] -> []
        | _ -> [injectivity_assertion]

        in

        let stmts_list = stmts_list @ [havoc_stmt; assume_stmt; eq_stmt; assert_heap_valid] in

        let stmt = Stmt.mk_block_stmt ~loc stmts_list in

        Rewriter.return stmt

      | e ->
        let* is_e_pure = Rewriter.ProgUtils.is_expr_pure e in
        if is_e_pure then
          let assert_expr = Expr.mk_binder ~loc:(Expr.to_loc e) ~typ:Type.bool ~trigs:(universal_quants.triggers) Forall (List.map univ_quants_list ~f:(fun (_, v_d) -> v_d)) (Expr.mk_impl (Expr.mk_and conds) e) in

          let assert_stmt = (Stmt.mk_assert_expr ~loc:(Expr.to_loc e) ~cmnt:(Some ((match cmnt with | None -> "" | Some cmnt -> cmnt) ^ "\nexhale: " ^ (Stdlib.Format.asprintf "%a" Expr.pr (Expr.mk_binder Forall univ_vars_list (Expr.mk_impl (Expr.mk_and conds) expr))))) assert_expr) in
          (* let assume_stmt = (Stmt.mk_assume_expr ~loc:(Expr.to_loc e) assert_expr) in *)
          (* Rewriter.return (Stmt.mk_block_stmt ~loc:(Expr.to_loc e) [assume_stmt; assert_stmt]) *)
          Rewriter.return assert_stmt
        else
          match e with
          | App (Var qual_ident, args, _) ->
            let* symbol = Rewriter.find_and_reify (Expr.to_loc e) qual_ident in
            begin match symbol with
            | CallDef c when Poly.(c.call_decl.call_decl_kind = Pred || c.call_decl.call_decl_kind = Invariant) ->

              let* heap_elem_type_qual_iden = Rewriter.ProgUtils.get_pred_utils_rep_type (Expr.to_loc e) qual_ident 
            
              in

              let heap_elem_type = Type.mk_var (Expr.to_loc e) heap_elem_type_qual_iden in
        
              let pred_name = qual_ident in
              let pred_heap_name = pred_heap_name pred_name in
              let pred_heap_qual_ident = QualIdent.from_ident pred_heap_name in
              let pred_heap_expr = Expr.mk_var ~typ:(Type.mk_map (Expr.to_loc e) Type.ref heap_elem_type) pred_heap_qual_ident in
        
              let pred_heap2_name = pred_heap_name2 pred_name in
              let pred_heap2_qual_ident = QualIdent.from_ident pred_heap2_name in
              let pred_heap2_expr = Expr.mk_var ~typ:(Type.mk_map (Expr.to_loc e) Type.ref heap_elem_type) pred_heap2_qual_ident in
        
              let* (pred_heapchunk_operator: qual_ident) = 
                Rewriter.ProgUtils.get_pred_utils_frame (Expr.to_loc e) pred_name
              in

              let* (pred_heap_valid_fn: qual_ident) = 
                Rewriter.ProgUtils.get_pred_utils_valid (Expr.to_loc e) pred_name
              in

              let* pred_in_types = Rewriter.ProgUtils.pred_in_types qual_ident in

              let* pred_out_types = Rewriter.ProgUtils.pred_out_types qual_ident in

              let* pred_ra_constr = Rewriter.ProgUtils.pred_ra_constr_qual_ident (Expr.to_loc e) qual_ident in

              let havoc_stmt = Stmt.mk_havoc ~loc pred_heap2_qual_ident in
              let assume_stmt = 
                let in_vars = List.map pred_in_types ~f:(fun tp -> 
                  Type.{ var_name = Ident.fresh (Expr.to_loc e) "in"; var_loc = Expr.to_loc e; 
                  var_type = tp; var_const = false; var_ghost = false; var_implicit = false; }
                ) in

                let in_vars_exprs = List.map in_vars ~f:(fun v -> Expr.from_var_decl v) in
                let in_vars_tuple = Expr.mk_tuple in_vars_exprs in
                
                
                (* let l_var = Type.{ var_name = Ident.fresh (Expr.to_loc expr) "l"; var_loc = Expr.to_loc expr; 
                var_type = Type.ref; var_const = false; var_ghost = false; var_implicit = false; } in *)

                (* let l_expr = Expr.mk_var ~typ:l_var.var_type (QualIdent.from_ident l_var.var_name) in *)

                let in_vars_eq_args = 
                  List.map2_exn in_vars (List.take args (List.length pred_in_types)) ~f:(fun var_decl arg -> 
                    Expr.mk_eq (Expr.from_var_decl var_decl) arg
                  )
                  
                in

                let new_chunk = 
                  let new_chunk_expr_list = match c.call_decl.call_decl_kind with 
                  | Pred -> [Expr.mk_int 1; Expr.mk_tuple (List.drop args (List.length pred_in_types))]
                  | Invariant -> [Expr.mk_tuple (List.drop args (List.length pred_in_types))]
                  | _ -> Error.error (Expr.to_loc e) "Internal error: Expected a predicate or invariant"

                  in
                  
                  Expr.mk_app ~loc ~typ:heap_elem_type (Expr.DataConstr pred_ra_constr) new_chunk_expr_list 
                in
                
                Stmt.mk_assume_expr ~loc 
                ~cmnt:(Some ((match cmnt with | None -> "" | Some cmnt -> cmnt) ^ "\nexhale: " ^ (Stdlib.Format.asprintf "%a" Expr.pr (Expr.mk_binder Forall univ_vars_list (Expr.mk_impl (Expr.mk_and conds) expr)))))

                (Expr.mk_binder ~trigs:[[Expr.mk_maplookup ~loc pred_heap2_expr in_vars_tuple]; [Expr.mk_maplookup ~loc pred_heap_expr in_vars_tuple]]
                
                ~loc ~typ:Type.bool Forall in_vars 
                  (Expr.mk_binder ~loc ~typ:Type.bool Forall univ_vars_list
                    (Expr.mk_app ~loc ~typ:Type.bool Expr.Ite [

                      (* m1(a,b,c) && l == f1(a, b, c) *)
                      Expr.mk_and ~loc (in_vars_eq_args @ conds);

                      (* pred$Heap2[l] == field.comp( field$Heap[l], f2(a, b, c) ) *)
                      Expr.mk_eq ~loc (Expr.mk_maplookup ~loc pred_heap2_expr in_vars_tuple)
                        (Expr.mk_app ~loc ~typ:heap_elem_type 
                          (Expr.Var pred_heapchunk_operator)  [
                            Expr.mk_maplookup ~loc pred_heap_expr in_vars_tuple;
                            new_chunk;
                          ] );

                  
                      (* pred$Heap2[l] == pred$Heap[l] *)
                      Expr.mk_eq ~loc (Expr.mk_maplookup ~loc pred_heap2_expr in_vars_tuple) 
                        (Expr.mk_maplookup ~loc pred_heap_expr in_vars_tuple);
                    ])
                  )
                )
              in

              (* pred$Heap := pred$Heap2 *)
              let eq_stmt = Stmt.mk_assign ~loc [pred_heap_expr] pred_heap2_expr in
              
              (* let* pred_valid_fn = Rewriter.ProgUtils.get_pred_utils_valid (Expr.to_loc expr) (Expr.to_qual_ident e2) in
              let heap_valid_stmt = Stmt.mk_assert_expr ~loc 
                (Expr.mk_app ~loc ~typ:Type.bool (Expr.Var pred_valid_fn) [pred_heap_expr])

              in *)

              let assert_heap_valid = Stmt.mk_assert_expr ~loc 
                (Expr.mk_app ~loc ~typ:Type.bool (Expr.Var pred_heap_valid_fn) [pred_heap_expr]) 
              
              in

              let* injectivity_assertion = generate_injectivity_assertions universal_quants conds (Expr.mk_tuple (List.take args (List.length pred_in_types))) in

              let stmts_list = match univ_quants_list with
              | [] -> []
              | _ -> [injectivity_assertion]

              in

              let stmts_list = stmts_list @ [havoc_stmt; assume_stmt; eq_stmt; assert_heap_valid] in

              let stmt = Stmt.mk_block_stmt ~loc stmts_list in

              Rewriter.return stmt
            | _ -> 
              Error.error (Expr.to_loc e) "Expected a predicate definition"
            end
          | _ ->
          unsupported_expr_error expr
  end

  let rec rewrite_make_heaps_explicit (s: Stmt.t) : Stmt.t Rewriter.t =
    let open Rewriter.Syntax in
  
    match s.stmt_desc with
    | Stmt.Basic basic_stmt -> 
      begin match basic_stmt with
      | Spec (spec_kind, spec) ->
        begin match spec_kind with
        | Inhale ->
          let expr = spec.spec_form in

          let* stmt = TrnslInhale.trnsl_inhale_expr ?cmnt:spec.spec_comment ~loc:s.stmt_loc expr in
          Rewriter.return stmt

        | Exhale ->
          let expr = spec.spec_form in

          let* stmt = TrnslExhale.trnsl_exhale_expr ?cmnt:spec.spec_comment ~loc:s.stmt_loc expr in
          Rewriter.return stmt
        | Assume -> 
          let expr = spec.spec_form in

          let* stmt = TrnslInhale.trnsl_assume_expr ?cmnt:spec.spec_comment ~loc:s.stmt_loc expr in
          Rewriter.return stmt
        | Assert ->
          let* is_e_pure = Rewriter.ProgUtils.is_expr_pure spec.spec_form in
          if is_e_pure then
            (* let assume_stmt = Stmt.mk_assume_expr ~loc:s.stmt_loc spec.spec_form in *)
            (* Rewriter.return (Stmt.mk_block_stmt ~loc:s.stmt_loc [s; assume_stmt]) *)
            (* The corresponding assume stmt is being added in backend/checker.ml *)
            Rewriter.return s
          else
            let nondet_var = Type.{ var_name = Ident.fresh s.stmt_loc "$nondet"; var_loc = s.stmt_loc; 
              var_type = Type.bool; var_const = true; var_ghost = false; var_implicit = false; } in

            let (nondet_var_def: Module.symbol) = VarDef {var_decl = nondet_var; var_init = None} in

            let* _ = Rewriter.introduce_symbol nondet_var_def in

            let* exhale_stmt = TrnslExhale.trnsl_exhale_expr ?cmnt:spec.spec_comment ~loc:s.stmt_loc spec.spec_form in
            let assume_false_stmt = Stmt.mk_assume_expr ~loc:s.stmt_loc (Expr.mk_bool false) in

            let cond_stmt = Stmt.Cond {
              cond_test = Expr.from_var_decl nondet_var; 
              cond_then = Stmt.mk_block_stmt ~loc:s.stmt_loc [exhale_stmt; assume_false_stmt];
              cond_else = Stmt.mk_block_stmt ~loc:s.stmt_loc []} in


            Rewriter.return Stmt.{stmt_desc = cond_stmt; stmt_loc = s.stmt_loc}
        end

      | FieldRead fr_desc ->
        let* lhs_var = Rewriter.find_and_reify s.stmt_loc fr_desc.field_read_lhs in
        let lhs_var = match lhs_var with
          | VarDef var_symbol -> var_symbol.var_decl
          | _ -> Error.type_error s.stmt_loc "Expected a variable definition."
        in

        let field_name = fr_desc.field_read_field in

        let* field_symbol = Rewriter.find_and_reify s.stmt_loc field_name in

        let field_symbol = match field_symbol with
          | FieldDef field_symbol -> field_symbol
          | _ -> Error.type_error s.stmt_loc "Expected a field definition."
        in

        let field_ra = Rewriter.ProgUtils.field_get_ra_qual_iden field_symbol in

        let* orig_ra_name, ra_def, _ = Rewriter.find s.stmt_loc field_ra in

        if (QualIdent.(orig_ra_name = Predefs.lib_frac_mod_qual_ident)) then

          let field_ra_type = Rewriter.ProgUtils.get_ra_rep_type field_ra in
          
          let field_heap_name = field_heap_name field_name in
          let field_heap_expr = Expr.mk_var ~typ:(Type.mk_map s.stmt_loc Type.ref field_ra_type) (QualIdent.from_ident field_heap_name) in

          let field_val_destr = QualIdent.append field_ra Predefs.lib_frac_chunk_destr1_ident in
          let field_frac_destr = QualIdent.append field_ra Predefs.lib_frac_chunk_destr2_ident in

          let assert_expr = Expr.mk_app ~loc:s.stmt_loc ~typ:Type.bool Expr.Gt [
            Expr.mk_app ~typ:Type.real (DataDestr field_frac_destr) [(Expr.mk_maplookup field_heap_expr fr_desc.field_read_ref)]; 
            
            Expr.mk_real 0.
          ] in
          
          let assert_stmt = Stmt.mk_assert_expr ~loc:s.stmt_loc assert_expr in
          let assign_stmt = Stmt.mk_assign ~loc:s.stmt_loc 
            [Expr.from_var_decl lhs_var] 
            (Expr.mk_app ~typ:lhs_var.var_type (DataDestr field_val_destr) [(Expr.mk_maplookup field_heap_expr fr_desc.field_read_ref)]) 
          in

          Rewriter.return (Stmt.mk_block_stmt ~loc:s.stmt_loc [assert_stmt; assign_stmt])

        else
          Error.type_error s.stmt_loc "Expected a FracRA type."

      | Assign {assign_lhs = [Expr.App (Read, [ref_expr; field_expr], _)]; assign_rhs} ->
        let field_name = Expr.to_qual_ident field_expr in

        let* field_symbol = Rewriter.find_and_reify s.stmt_loc field_name in

        let field_symbol = match field_symbol with
          | FieldDef field_symbol -> field_symbol
          | _ -> Error.type_error s.stmt_loc "Expected a field definition."
        in
        
        let field_ra = Rewriter.ProgUtils.field_get_ra_qual_iden field_symbol in

        let* orig_ra_name, ra_def, _ = Rewriter.find s.stmt_loc field_ra in

        if (QualIdent.(orig_ra_name = Predefs.lib_frac_mod_qual_ident)) then

          let field_ra_type = Rewriter.ProgUtils.get_ra_rep_type field_ra in
          
          let field_heap_name = field_heap_name field_name in
          let field_heap_expr = Expr.mk_var ~typ:(Type.mk_map s.stmt_loc Type.ref field_ra_type) (QualIdent.from_ident field_heap_name) in

          let field_frac_destr = QualIdent.append field_ra Predefs.lib_frac_chunk_destr2_ident in
          let field_frac_constr = QualIdent.append field_ra Predefs.lib_frac_chunk_constr_ident in

          let assert_expr = Expr.mk_app ~loc:s.stmt_loc ~typ:Type.bool Expr.Geq [
            Expr.mk_app ~typ:Type.real (DataDestr field_frac_destr) [(Expr.mk_maplookup field_heap_expr ref_expr)]; 
            
            Expr.mk_real 1.
          ] in

          let new_val = Expr.mk_app ~typ:field_ra_type (DataConstr field_frac_constr) [assign_rhs; Expr.mk_real 1.] in
          
          let assert_stmt = Stmt.mk_assert_expr ~loc:s.stmt_loc assert_expr in
          let assign_stmt = Stmt.mk_assign ~loc:s.stmt_loc 
            [field_heap_expr] 
            (Expr.mk_app ~typ:(Type.mk_map s.stmt_loc Type.ref field_ra_type) MapUpdate  [field_heap_expr; ref_expr; new_val]) 
          in

          Rewriter.return (Stmt.mk_block_stmt ~loc:s.stmt_loc [assert_stmt; assign_stmt])

        else
          Error.type_error s.stmt_loc "Expected a FracRA type."


      | _ -> Rewriter.return s
      end 
    | _ -> 
      let* s = Rewriter.Stmt.descend s ~f:rewrite_make_heaps_explicit in
  
      Rewriter.return s
end



let rewrite_introduce_heaps (c: Callable.t) : Callable.t Rewriter.t =
  let open Rewriter.Syntax in
  Logs.debug (fun m -> m "Rewrites.rewrite_introduce_heaps: Introducing heaps in callable: %a" Ident.pr c.call_decl.call_decl_name);
  match c.call_def with
  | FuncDef _ -> 
    Rewriter.return c

  | ProcDef {proc_body = None} ->
    Rewriter.return c
  
  | ProcDef {proc_body = Some body} -> 
    let* preds_list = stmt_preds_mentioned body in
    let fields_list = Stmt.stmt_fields_accessed body in
    let au_preds_list = Set.to_list (Stmt.stmt_au_preds_referenced body) in

    Logs.debug (fun m -> m "Rewrites.rewrite_introduce_heaps: Predicates mentioned in the body");

    let* body = HeapsExplicitTrnsl.introduce_heaps_in_stmts ~loc:c.call_decl.call_decl_loc ~fields_list ~preds_list ~au_preds_list body in

    (* let* body = HeapsExplicitTrnsl.rewrite_make_heaps_explicit body in *)

    Rewriter.return { c with call_def = ProcDef { proc_body = Some body; } }
  

    

let rec rewrite_ssa_stmts (s: Stmt.t) : (Stmt.t, var_decl ident_map) Rewriter.t_ext =
  let open Rewriter.Syntax in

  let* var_map = Rewriter.current_user_state in
  let subst_map = Map.map var_map ~f:(fun var_decl -> Expr.from_var_decl var_decl) in
  let subst_map = (Map.map_keys_exn (module QualIdent)) subst_map ~f:(fun ident -> QualIdent.from_ident ident) in

  match s.stmt_desc with

  | Basic basic_stmt -> begin
    match basic_stmt with
    | Spec (spec_kind, spec) ->
      let spec_form = Expr.alpha_renaming spec.spec_form subst_map in

      Rewriter.return Stmt.{ s with stmt_desc = Basic (Spec (spec_kind, { spec with spec_form; })) }

    | Assign assign_stmt ->
      let assign_rhs = Expr.alpha_renaming assign_stmt.assign_rhs subst_map in
      let* assign_lhs = Rewriter.List.map assign_stmt.assign_lhs ~f:(fun lhs_expr -> 
        if Expr.is_ident lhs_expr then
          let local_var = Expr.to_ident lhs_expr in

          Logs.debug (fun m -> m "Rewrites.rewrite_ssa_stmts: Assigning to local variable %a; for stmt %a" Ident.pr local_var Stmt.pr s);
          let old_var_decl = Map.find_exn var_map local_var in
          let new_var_decl = { old_var_decl with var_name = Ident.fresh old_var_decl.var_loc old_var_decl.var_name.ident_name } in

          let* _ = Rewriter.introduce_symbol (VarDef { var_decl = new_var_decl; var_init = None }) in

          let var_map = Map.set var_map ~key:local_var ~data:new_var_decl in

          let+ _ = Rewriter.set_user_state var_map in

          Expr.from_var_decl new_var_decl

        else
          Rewriter.return lhs_expr
      ) 
      
      in

      Rewriter.return Stmt.{ s with stmt_desc = Basic (Assign { assign_lhs; assign_rhs; }) }
      
    | Havoc qual_iden ->
      if QualIdent.is_local qual_iden then
        let local_var = QualIdent.to_ident qual_iden in

        Logs.debug (fun m -> m "Rewrites.rewrite_ssa_stmts: Havocing local variable %a" Ident.pr local_var);
        let old_var_decl = Map.find_exn var_map local_var in
        let new_var_decl = { old_var_decl with var_name = Ident.fresh old_var_decl.var_loc old_var_decl.var_name.ident_name } in

        let* _ = Rewriter.introduce_symbol (VarDef { var_decl = new_var_decl; var_init = None }) in

        let var_map = Map.set var_map ~key:local_var ~data:new_var_decl in

        let+ _ = Rewriter.set_user_state var_map in

        Stmt.mk_block_stmt ~loc:s.stmt_loc []

      else
        Rewriter.return s
    
    | Bind bind_stmt -> 
      let bind_rhs = Expr.alpha_renaming bind_stmt.bind_rhs subst_map in
      let* bind_lhs = Rewriter.List.map bind_stmt.bind_lhs ~f:(fun lhs_expr -> 
        if Expr.is_ident lhs_expr then
          let local_var = Expr.to_ident lhs_expr in

          let old_var_decl = Map.find_exn var_map local_var in
          let new_var_decl = { old_var_decl with var_name = Ident.fresh old_var_decl.var_loc old_var_decl.var_name.ident_name } in

          let* _ = Rewriter.introduce_symbol (VarDef { var_decl = new_var_decl; var_init = None }) in

          let var_map = Map.set var_map ~key:local_var ~data:new_var_decl in

          let+ _ = Rewriter.set_user_state var_map in

          Expr.from_var_decl new_var_decl

        else
          Rewriter.return lhs_expr
      ) 
      
      in

      Rewriter.return Stmt.{ s with stmt_desc = Basic (Bind { bind_lhs; bind_rhs; }) }
  
    | _ -> 
      Logs.debug (fun m -> m "Rewrites.rewrite_ssa_stmts: Skipping statement %a" Stmt.pr s);
      assert false
  end

  | Block block_stmt -> 
    let+ block_body = Rewriter.List.map block_stmt.block_body ~f:rewrite_ssa_stmts in

    Stmt.mk_block_stmt ~ghost:block_stmt.block_is_ghost ~loc:s.stmt_loc block_body

    (* { s with stmt_desc = Block { block_stmt with block_body; } } *)
    

  
  | Cond cond_stmt -> 
    let cond_test = Expr.alpha_renaming cond_stmt.cond_test subst_map in

    let* cond_then = rewrite_ssa_stmts cond_stmt.cond_then in

    let* cond_then_map = Rewriter.current_user_state in

    let* _ = Rewriter.set_user_state var_map in
    let* cond_else = rewrite_ssa_stmts cond_stmt.cond_else in

    let* cond_else_map = Rewriter.current_user_state in

    let updated_vals = Map.fold2 cond_then_map cond_else_map ~init:[] ~f:(fun ~key ~data acc ->
      match data with
      | `Both (then_var_decl, else_var_decl) -> 
        if Ident.(Type.(then_var_decl.var_name) = Type.(else_var_decl.var_name)) then
          acc
        else
          key :: acc
      
      | `Left _ | `Right _ -> Error.error s.stmt_loc "Mismatched variable declarations in then and else branches."
    
    ) in


    let* new_var_map = Rewriter.List.fold_left updated_vals ~init:var_map ~f:(fun map var -> 
      let old_var_decl = Map.find_exn var_map var in
      let new_var_decl = { old_var_decl with var_name = Ident.fresh old_var_decl.var_loc old_var_decl.var_name.ident_name } in

      let+ _ = Rewriter.introduce_symbol (VarDef { var_decl = new_var_decl; var_init = None }) in

      Map.set map ~key:var ~data:new_var_decl
    ) in

    let cond_then_assigns = List.map updated_vals ~f:(fun var -> 
      let old_var_decl = Map.find_exn cond_then_map var in
      let new_var_decl = Map.find_exn new_var_map var in

      Stmt.mk_assign ~loc:s.stmt_loc [Expr.from_var_decl new_var_decl] (Expr.from_var_decl old_var_decl)
    ) in

    let cond_then = Stmt.mk_block_stmt ~loc:s.stmt_loc ( cond_then :: cond_then_assigns) in

    let cond_else_assigns = List.map updated_vals ~f:(fun var -> 
      let old_var_decl = Map.find_exn cond_else_map var in
      let new_var_decl = Map.find_exn new_var_map var in

      Stmt.mk_assign ~loc:s.stmt_loc [Expr.from_var_decl new_var_decl] (Expr.from_var_decl old_var_decl)
    ) in

    let cond_else = Stmt.mk_block_stmt ~loc:s.stmt_loc ( cond_else :: cond_else_assigns) in

    let+ _ = Rewriter.set_user_state new_var_map in

    Stmt.{ s with stmt_desc = Cond { cond_test; cond_then; cond_else; } }

  | Loop loop_stmt -> assert false

let rewrite_ssa_transform  (c: Callable.t) : (Callable.t, var_decl ident_map) Rewriter.t_ext =
  let open Rewriter.Syntax in

  match c.call_def with
  | FuncDef _ | ProcDef {proc_body = None} -> 
    Rewriter.return c

  | ProcDef { proc_body = Some body } ->

    let init_map = List.fold (c.call_decl.call_decl_formals @ c.call_decl.call_decl_returns @ c.call_decl.call_decl_locals) ~init:(Map.empty (module Ident)) ~f:(fun map var_decl -> 
      Map.add_exn map ~key:var_decl.var_name ~data:var_decl
    ) in

    let* _ = Rewriter.set_user_state init_map in

    Logs.debug (fun m -> m "Rewrites.rewrite_ssa_transform: Starting rewrites on callable %a" Callable.pr c);

    let+ body = rewrite_ssa_stmts body in
    
    { c with call_def = ProcDef { proc_body = Some body; } }

let rec rewrite_assign_stmts (s: Stmt.t) : Stmt.t Rewriter.t =
  let open Rewriter.Syntax in

  Logs.debug (fun m -> m "Rewrites.rewrite_assign_stmts: Starting rewrites on statement %a" Stmt.pr s);

  match s.stmt_desc with
  | Basic (Assign assign_stmt) ->
    let assume_stmt = Stmt.mk_assume_expr ~loc:s.stmt_loc (Expr.mk_eq (Expr.mk_tuple assign_stmt.assign_lhs) assign_stmt.assign_rhs) in

    Rewriter.return assume_stmt

  | _ -> 
    let* s = Rewriter.Stmt.descend s ~f:rewrite_assign_stmts in
  
    Rewriter.return s
    

let rec all_rewrites (m: Module.t) : Module.t Rewriter.t =
  let open Rewriter.Syntax in
  Logs.debug (fun m -> m "Rewrites.all_rewrites: Starting rewrites");

  Logs.debug (fun m1 -> m1 "Rewrites.all_rewrites: Starting rewrite_compr_expr on module %a" Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_expressions ~f:rewrite_compr_expr m in

  Logs.debug (fun m1 -> m1 "Rewrites.all_rewrites: Starting rewrite_set_diff_expr on module %a" Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_expressions ~f:rewrite_set_diff_expr m in

  Logs.debug (fun m1 -> m1 "Rewrites.all_rewrites: Starting rewrite_loops on module %a" Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_stmts ~f:rewrite_loops m in

  Logs.debug (fun m1 -> m1 "Rewrites.all_rewrites: Starting rewrite_atomic_callable_token on module %a" Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_callables ~f:rewrite_atomic_callable_token m in

  Logs.debug (fun m1 -> m1 "Rewrites.all_rewrites: Starting rewrite_au_cmnds on module %a" Ident.pr m.mod_decl.mod_decl_name);
  let* m =
    Rewriter.eval_with_user_state ~init:{AtomicityAnalysis.au_opened = []; invs_opened = []; atomic_step_taken = false}
    (Rewriter.Module.rewrite_stmts ~f:(AtomicityAnalysis.rewrite_au_cmnds ~ghost_block:false) m) 
  in 

  Logs.debug (fun m1 -> m1 "Rewrites.all_rewrites: Starting rewrite_fold_unfold_stmts on module %a" Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_stmts ~f:rewrite_fold_unfold_stmts m in

  Logs.debug (fun m1 -> m1 "Rewrites.all_rewrites: Starting rewrite_call_stmts on module %a" Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_stmts ~f:rewrite_call_stmts m in

  Logs.debug (fun m1 -> m1 "Rewrites.all_rewrites: Starting rewrite_ret_stmts on module %a" Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_stmts ~f:rewrite_ret_stmts m in

  Logs.debug (fun m1 -> m1 "Rewrites.all_rewrites: Starting rewrite_frac_field_types on module %a" Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rec_rewrite_symbols ~f:rewrite_frac_field_types m in
  
  Logs.debug (fun m1 -> m1 "Rewrites.all_rewrites: Starting rewrite_own_expr_4_arg on module %a" Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_expressions ~f:rewrite_own_expr_4_arg m in

  Logs.debug (fun m1 -> m1 "Rewrites.all_rewrites: Starting rewrite_new_stmt_heap_arg on module %a" Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_stmts ~f:rewrite_new_stmt_heap_arg m in
  
  Logs.debug (fun m1 -> m1 "Rewrites.all_rewrites: Starting rewrite_new_stmts on module %a" Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_stmts ~f:rewrite_new_stmts m in

  Logs.debug (fun m1 -> m1 "Rewrites.all_rewrites: Starting rewrite_add_predicate_validity_lemmas on module %a" Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_callables ~f:rewrite_add_predicate_validity_lemmas m in

  Logs.debug (fun m1 -> m1 "Rewrites.all_rewrites: Starting rewrite_callable_pre_post_conds on module %a" Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_callables ~f:rewrite_callable_pre_post_conds m in

  Logs.debug (fun m1 -> m1 "Rewrites.all_rewrites: Starting rewrite_add_field_utils on module %a" Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rec_rewrite_symbols ~f:HeapsExplicitTrnsl.rewrite_add_field_utils m in

  Logs.debug (fun m1 -> m1 "Rewrites.all_rewrites: Starting rewrite_add_pred_utils on module %a" Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_callables ~f:HeapsExplicitTrnsl.rewrite_add_pred_utils m in

  Logs.debug (fun m1 -> m1 "Rewrites.all_rewrites: Starting rewrite_add_atomics_utils on module %a" Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_callables ~f:HeapsExplicitTrnsl.rewrite_add_atomics_utils m in

  Logs.debug (fun m1 -> m1 "Rewrites.all_rewrites: Starting rewriter_skolemize_inhale_stmts on module %a" Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_stmts ~f:HeapsExplicitTrnsl.TrnslInhale.rewriter_skolemize_inhale_stmts m in

  Logs.debug (fun m1 -> m1 "Rewrites.all_rewrites: Starting rewriter_eliminate_binds_for_inhale on module %a" Ident.pr m.mod_decl.mod_decl_name);
  let* m = 
    Rewriter.eval_with_user_state ~init:None
    (Rewriter.Module.rewrite_stmts ~f:HeapsExplicitTrnsl.TrnslInhale.rewriter_eliminate_binds_for_inhale m) in

  Logs.debug (fun m1 -> m1 "Rewrites.all_rewrites: Starting rewriter_user_annot_elim_exists_from_exhales on module %a" Ident.pr m.mod_decl.mod_decl_name);
  let* m = 
    Rewriter.eval_with_user_state ~init:None
    (Rewriter.Module.rewrite_stmts ~f:HeapsExplicitTrnsl.TrnslExhale.rewriter_user_annot_elim_exists_from_exhales m) in

  Logs.debug (fun m1 -> m1 "Rewrites.all_rewrites: Starting rewrite_introduce_heaps on module %a" Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_callables ~f:rewrite_introduce_heaps m in

  Logs.debug (fun m1 -> m1 "Rewrites.all_rewrites: Starting rewriter_find_witness_elim_exists_from_exhale on module %a" Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_stmts ~f:HeapsExplicitTrnsl.TrnslExhale.rewriter_find_witness_elim_exists_from_exhale m in

  Logs.debug (fun m1 -> m1 "Rewrites.all_rewrites: Starting rewrite_make_heaps_explicit on module %a" Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_stmts ~f:HeapsExplicitTrnsl.rewrite_make_heaps_explicit m in

  Logs.debug (fun m1 -> m1 "Rewrites.all_rewrites: Starting rewrite_ssa_transform on module %a: %a" Ident.pr m.mod_decl.mod_decl_name Module.pr m);
  let* m = 
    Rewriter.eval_with_user_state ~init:(Map.empty (module Ident))
    (Rewriter.Module.rewrite_callables ~f:rewrite_ssa_transform m) in

  Logs.debug (fun m1 -> m1 "Rewrites.all_rewrites: Starting rewrite_assign_stmts on module %a" Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_stmts ~f:rewrite_assign_stmts m in


  (* TODO: havoc return vars before inhaling *)

  let* tbl = Rewriter.get_table in
  (* Logs.debug (fun m -> m "Rewrites.all_rewrites: SymbolTbl Symbols: \n%a\n" (Util.Print.pr_list_comma (fun ppf (k,v) -> Stdlib.Format.fprintf ppf "%a -> %a" QualIdent.pr k Module.pr_symbol v)) (Map.to_alist (Map.filter_keys tbl.tbl_symbols ~f:(fun k -> Poly.((QualIdent.to_string k) = "$Program.pr"))))); *)

  Rewriter.return m



let process_module ?(tbl = SymbolTbl.create ()) (m: Module.t) = 
  assert (SymbolTbl.curr_is_root tbl);
  (* assert Ident.(m.mod_decl.mod_decl_name = QualIdent.to_ident (SymbolTbl.root_ident tbl)); *)
  Rewriter.eval (all_rewrites m) tbl
