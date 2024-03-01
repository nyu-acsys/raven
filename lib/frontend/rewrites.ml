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
      
      { Stmt.spec_form = spec_form;
        spec_atomic = false;
        spec_error = None;
      } 
      
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
      
      { Stmt.spec_form = spec_form;
        spec_atomic = false;
        spec_error = None;
      } 
      
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
  
    let* loop_arg_var_decls, loop_arg_renaming_map, loop_arg_renaming_qual_ident_map, curr_loop_arg_var_decls = 
      begin
        (* Local variables accessed from loop body become arguments for loop procedure *)
        let curr_loop_args = Stmt.local_vars_accessed loop.loop_postbody |> Set.to_list in
        let+ curr_loop_arg_var_decls = Rewriter.List.map curr_loop_args ~f:(fun var -> 
          let+ symbol = Rewriter.find_and_reify var.ident_loc (QualIdent.from_ident var) in
          
          (match symbol with
          | VarDef v -> v.var_decl
          | _ -> Error.error stmt.stmt_loc ("Expected a variable (1); found " ^ (Symbol.to_string symbol)))
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
  | Basic (Return ret_expr_list) ->

    let* callable_decl =
      let* curr_proc_name = Rewriter.current_scope_id in

      Logs.debug (fun m -> m "Rewrites.rewrite_ret_stmts: curr_proc_name: %a" QualIdent.pr curr_proc_name);

      let+ symbol = Rewriter.find_and_reify stmt.stmt_loc curr_proc_name in
          
      (match symbol with
      | CallDef c -> 
        Logs.debug (fun m -> m "Rewrites.rewrite_ret_stmts: curr_proc: %a" Callable.pr c);      
        c.call_decl
      | _ -> Error.error stmt.stmt_loc "Expected a call_def")
    
    in

    let postconds_spec = callable_decl.call_decl_postcond in

    let postconds_exhale_stmts = List.map postconds_spec ~f:(fun spec -> Stmt.mk_exhale_spec ~loc:stmt.stmt_loc spec) in

    let assume_false = Stmt.mk_assume_expr ~loc:stmt.stmt_loc (Expr.mk_bool ~loc:stmt.stmt_loc false) in

    let new_stmt = Stmt.mk_block_stmt ~loc:stmt.stmt_loc (postconds_exhale_stmts @ [assume_false]) in

    Rewriter.return new_stmt


  | _ -> Rewriter.Stmt.descend stmt ~f:rewrite_ret_stmts


let rec rewrite_new_stmts (stmt: Stmt.t) : Stmt.t Rewriter.t =
  let open Rewriter.Syntax in
  match stmt.stmt_desc with
  | Basic (New new_desc) ->

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

    let inhale_expr = Expr.mk_app ~loc:stmt.stmt_loc Expr.Own 
      [Expr.mk_var ~loc:stmt.stmt_loc ~typ:Type.ref new_desc.new_lhs;
      Expr.mk_var ~loc:stmt.stmt_loc ~typ:field_type field_name;
      field_val;
      ]
    in

    let inhale_stmt = Stmt.mk_inhale_expr ~loc:stmt.stmt_loc inhale_expr in

    Rewriter.return inhale_stmt
      
    )

    in

    Rewriter.return (Stmt.mk_block_stmt ~loc:stmt.stmt_loc new_stmts)



  | _ -> Rewriter.Stmt.descend stmt ~f:rewrite_ret_stmts


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
      let truncated_formal_args, dropped_formal_args = List.split_n pred_decl.call_decl_formals (List.length use_desc.use_args) in

      let fresh_dropped_args = List.map dropped_formal_args ~f:(fun var_decl -> 
        { var_decl with var_name = Ident.fresh stmt.stmt_loc var_decl.var_name.ident_name; var_loc = stmt.stmt_loc; }
      ) in

      let fresh_dropped_args_exprs = List.map fresh_dropped_args ~f:(Expr.from_var_decl) in
      
      let renaming_map = List.fold2_exn (truncated_formal_args @ dropped_formal_args) (use_desc.use_args @ fresh_dropped_args_exprs) ~init:((Map.empty (module QualIdent))) ~f:(fun map var_decl arg_expr ->
        Map.add_exn map ~key:(QualIdent.from_ident var_decl.var_name) ~data:arg_expr
      )
      in

      renaming_map, fresh_dropped_args
    in
    
    let body_expr = 
      let new_body = Expr.alpha_renaming body renaming_map in
      
      Expr.mk_binder ~loc:stmt.stmt_loc ~typ:Type.bool Exists fresh_dropped_args new_body 
    in

    let pred_expr = Expr.mk_app ~loc:stmt.stmt_loc ~typ:Type.bool (Expr.Var use_desc.use_name) use_desc.use_args in

    let new_stmt = 
      let inhale_stmt, exhale_stmt =
        match use_desc.use_kind with
        | Fold -> 
          Stmt.mk_inhale_expr ~loc:stmt.stmt_loc pred_expr, 
          Stmt.mk_exhale_expr ~loc:stmt.stmt_loc body_expr
        | Unfold -> 
          Stmt.mk_inhale_expr ~loc:stmt.stmt_loc body_expr,
          Stmt.mk_exhale_expr ~loc:stmt.stmt_loc pred_expr 

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

    let* renaming_map, dropped_args = 
      let truncated_formal_args, dropped_formal_args = List.split_n call_decl.call_decl_formals (List.length call_desc.call_args) in

      let fresh_dropped_args = List.map dropped_formal_args ~f:(fun var_decl -> 
        { var_decl with var_name = Ident.fresh stmt.stmt_loc var_decl.var_name.ident_name; var_loc = stmt.stmt_loc; }
      ) in

      let fresh_dropped_args_exprs = List.map fresh_dropped_args ~f:(Expr.from_var_decl) in

      (* Need to ensure that call_decl_returns and call_desc.call_lhs line up *)
      let* lhs_list = Rewriter.List.map call_desc.call_lhs ~f:(fun qual_iden -> let* symbol = Rewriter.find_and_reify stmt.stmt_loc qual_iden in
      
      match symbol with
      | VarDef v -> Rewriter.return (Expr.from_var_decl v.var_decl)
      | _ -> Error.error stmt.stmt_loc ("Expected a variable (3); found " ^ (Symbol.to_string symbol))
      ) in
      
      let renaming_map = List.fold2_exn (truncated_formal_args @ dropped_formal_args @ call_decl.call_decl_returns) (call_desc.call_args @ fresh_dropped_args_exprs @ lhs_list) ~init:((Map.empty (module QualIdent))) ~f:(fun map var_decl arg_expr ->
        Map.add_exn map ~key:(QualIdent.from_ident var_decl.var_name) ~data:arg_expr
      )
      in

      Rewriter.return (renaming_map, fresh_dropped_args)
    in

    (match call_def with
    | ProcDef _ -> 
      let build_correct_spec (spec: Stmt.spec) =
        (* renames args from old to new. Also, existentially quantifies over relevant implicit variables. *)
        let spec_form = Expr.alpha_renaming spec.spec_form renaming_map in

        let used_implicit_vars = List.filter dropped_args ~f:(
          fun var_decl -> 
            Set.mem (Expr.local_vars spec_form) var_decl.var_name
        ) in

        let spec_form = Expr.mk_binder ~loc:stmt.stmt_loc ~typ:Type.bool Exists used_implicit_vars spec_form in

        { spec with spec_form }
      in

      let exhale_stmts = List.map call_decl.call_decl_precond ~f:(fun spec -> Stmt.mk_exhale_spec ~loc:stmt.stmt_loc (build_correct_spec spec)) in

      (* TODO: Make sure implicit vars that appear in postconditions are being treated properly *)
      let inhale_stmts = List.map call_decl.call_decl_postcond ~f:(fun spec -> Stmt.mk_inhale_spec ~loc:stmt.stmt_loc (build_correct_spec spec)) in

      (* TODO: Need to havoc ret vars before inhaling postconditions *)
      let new_stmt = Stmt.mk_block_stmt ~loc:stmt.stmt_loc (exhale_stmts @ inhale_stmts) in
      
      Rewriter.return new_stmt

    | FuncDef _ -> 
      let exhale_stmts = List.map call_decl.call_decl_precond ~f:(fun spec -> Stmt.mk_exhale_spec ~loc:stmt.stmt_loc spec) in

      let new_stmt = Stmt.mk_block_stmt ~loc:stmt.stmt_loc (exhale_stmts @ [stmt]) in
      
      Rewriter.return new_stmt
    )


  | _ -> Rewriter.Stmt.descend stmt ~f:rewrite_call_stmts


let rewrite_callable_pre_post_conds (c: Callable.t) : Callable.t Rewriter.t =
  match c.call_def with
  | ProcDef proc ->
    (match proc.proc_body with
    | None -> Rewriter.return c
    | Some body ->
      let pre_conds = List.map c.call_decl.call_decl_precond ~f:(fun spec -> Stmt.mk_inhale_spec ~loc:(Expr.to_loc spec.spec_form) spec) and post_conds = List.map c.call_decl.call_decl_postcond ~f:(fun spec -> Stmt.mk_exhale_spec ~loc:(Expr.to_loc spec.spec_form) spec) in
      let new_body = Stmt.mk_block_stmt ~loc:(Stmt.loc body) (pre_conds @ [body] @ post_conds) in
      let new_proc = Callable.{ call_decl = c.call_decl; call_def = ProcDef { proc_body = Some new_body } } in
      Rewriter.return new_proc
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
  match expr with
  | App (Own, expr1 :: expr2 :: expr3 :: expr4 :: [], expr_attr) ->

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

  | _ -> Rewriter.Expr.descend expr ~f:rewrite_compr_expr


let rec expr_preds_mentioned (expr: Expr.t) : (QualIdent.t list) Rewriter.t =
  let open Rewriter.Syntax in 
  match expr with
  | App (Var qual_ident, _, _) ->
    let+ _, (_, symbol, _) = Rewriter.resolve_and_find (Expr.to_loc expr) qual_ident in

    (match symbol with
    | CallDef c -> 
      (match c.call_decl.call_decl_kind with
      | Pred -> [qual_ident]
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
      
    { Stmt.spec_form = spec_form;
      spec_atomic = false;
      spec_error = None;
    } 

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


  let rewrite_add_field_utils (symbol: Module.symbol) : Module.symbol Rewriter.t =
    let open Rewriter.Syntax in
    match symbol with
    | FieldDef f ->
      let* utils_module = 
        (* 
        module f$utils {
          type T = f.field_type.T;

          var id : T;

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

        let fld_elem_type = match f.field_type with
          | App (Fld, [tp_expr], _) -> tp_expr
          | _ -> Error.type_error f.field_loc "Expected field identifier." 
        
        in

        let mod_name = Rewriter.ProgUtils.field_utils_module_ident f.field_loc f.field_name in

        let mod_decl = {
          Module.mod_decl_name = mod_name;
          mod_decl_formals = [];
          mod_decl_returns = None;
          mod_decl_interfaces = Set.empty (module QualIdent);
          mod_decl_rep = None;
          mod_decl_is_ra = false;
          mod_decl_is_interface = false;
          mod_decl_loc = f.field_loc;
        } 
          
        in

        let* mod_def =
          let type_ident = Ident.make f.field_loc "T" 0 in
          let type_tp_expr = Type.mk_var f.field_loc (QualIdent.from_ident type_ident) in

          let type_def = {
            Module.type_def_name = type_ident;
            type_def_expr = Some fld_elem_type;
            type_def_rep = true;
            type_def_loc = f.field_loc;
          } in

          let var_def = {
            Stmt.var_decl = 
              Type.mk_var_decl ~loc:f.field_loc ~const:true (Rewriter.ProgUtils.field_utils_id_ident f.field_loc) type_tp_expr;
            var_init = Some (Expr.mk_var ~loc:f.field_loc ~typ:fld_elem_type (Rewriter.ProgUtils.field_get_ra_id f));
          } in

          let heap_valid_fn_decl = {
            Callable.call_decl_kind = Func;
            call_decl_name = Rewriter.ProgUtils.field_utils_valid_ident f.field_loc;
            call_decl_formals = [
              Type.mk_var_decl ~loc:f.field_loc ~const:true (Ident.fresh f.field_loc "h") (Type.mk_map f.field_loc Type.ref type_tp_expr)
            ];
            call_decl_returns = [
              Type.mk_var_decl ~loc:f.field_loc ~const:true (Ident.fresh f.field_loc "ret") Type.bool
            ];
            call_decl_locals = [];
            call_decl_precond = [];
            call_decl_postcond = [];
            call_decl_is_free = false;
            call_decl_is_auto = false;
            call_decl_loc = f.field_loc;
          } in

          let l_var_decl = 
            Type.mk_var_decl ~loc:f.field_loc ~const:true (Ident.fresh f.field_loc "l") Type.ref
          in

          let ra_valid_fn_qual_ident = Rewriter.ProgUtils.get_ra_valid_fn_qual_ident f in

          let heap_valid_fn = {
            Callable.call_decl = heap_valid_fn_decl;
            call_def = FuncDef { func_body = Some (
              Expr.mk_binder ~loc:f.field_loc ~typ:Type.bool Forall [l_var_decl] (
                  Expr.mk_app ~loc:f.field_loc ~typ:Type.bool (Expr.Var ra_valid_fn_qual_ident) [
                Expr.mk_maplookup ~loc:f.field_loc (Expr.from_var_decl (List.hd_exn heap_valid_fn_decl.call_decl_formals)) (Expr.from_var_decl l_var_decl)
                ]
              )
            )
            }
          }
          
          in


          let heap_add_chunk_fn_decl = {
            Callable.call_decl_kind = Func;
            call_decl_name = Rewriter.ProgUtils.field_utils_comp_chunk_ident f.field_loc;
            call_decl_formals = [
              Type.mk_var_decl ~loc:f.field_loc ~const:true (Ident.fresh f.field_loc "x1") type_tp_expr;
              Type.mk_var_decl ~loc:f.field_loc ~const:true (Ident.fresh f.field_loc "x2") type_tp_expr;
            ];
            call_decl_returns = [
              Type.mk_var_decl ~loc:f.field_loc ~const:true (Ident.fresh f.field_loc "ret") type_tp_expr;
            ];
            call_decl_locals = [];
            call_decl_precond = [];
            call_decl_postcond = [];
            call_decl_is_free = false;
            call_decl_is_auto = false;
            call_decl_loc = f.field_loc;
          } in

          let heap_add_chunk_fn = {
            Callable.call_decl = heap_add_chunk_fn_decl;
            call_def = FuncDef { func_body = Some (
              Expr.mk_app ~loc:f.field_loc ~typ:type_tp_expr (Expr.Var (Rewriter.ProgUtils.get_ra_comp_fn_qual_ident f)) [
                Expr.from_var_decl (List.hd_exn heap_add_chunk_fn_decl.call_decl_formals);
                Expr.from_var_decl (List.nth_exn heap_add_chunk_fn_decl.call_decl_formals 1)
              ]
            )
            }
          } 
        
          in


          let heap_sub_chunk_fn_decl = {
            Callable.call_decl_kind = Func;
            call_decl_name = Rewriter.ProgUtils.field_utils_frame_chunk_ident f.field_loc;
            call_decl_formals = [
              Type.mk_var_decl ~loc:f.field_loc ~const:true (Ident.fresh f.field_loc "x1") type_tp_expr;
              Type.mk_var_decl ~loc:f.field_loc ~const:true (Ident.fresh f.field_loc "x2") type_tp_expr;
            ];
            call_decl_returns = [
              Type.mk_var_decl ~loc:f.field_loc ~const:true (Ident.fresh f.field_loc "ret") type_tp_expr;
            ];
            call_decl_locals = [];
            call_decl_precond = [];
            call_decl_postcond = [];
            call_decl_is_free = false;
            call_decl_is_auto = false;
            call_decl_loc = f.field_loc;
          } in

          let heap_sub_chunk_fn = {
            Callable.call_decl = heap_sub_chunk_fn_decl;
            call_def = FuncDef { func_body = Some (
              Expr.mk_app ~loc:f.field_loc ~typ:type_tp_expr (Expr.Var (Rewriter.ProgUtils.get_ra_frame_fn_qual_ident f)) [
                Expr.from_var_decl (List.hd_exn heap_sub_chunk_fn_decl.call_decl_formals);
                Expr.from_var_decl (List.nth_exn heap_sub_chunk_fn_decl.call_decl_formals 1)
              ]
            )
            }
          } 
        
          in

          let heapchunk_compare_fn_decl = {
            Callable.call_decl_kind = Func;
            call_decl_name = Rewriter.ProgUtils.field_utils_heapchunk_compare_id f.field_loc;
            call_decl_formals = [
              Type.mk_var_decl ~loc:f.field_loc ~const:true (Ident.fresh f.field_loc "x1") type_tp_expr;
              Type.mk_var_decl ~loc:f.field_loc ~const:true (Ident.fresh f.field_loc "x2") type_tp_expr;
            ];
            call_decl_returns = [
              Type.mk_var_decl ~loc:f.field_loc ~const:true (Ident.fresh f.field_loc "ret") Type.bool;
            ];
            call_decl_locals = [];
            call_decl_precond = [];
            call_decl_postcond = [];
            call_decl_is_free = false;
            call_decl_is_auto = false;
            call_decl_loc = f.field_loc;
          } in



          let heapchunk_compare_fn = {
            Callable.call_decl = heapchunk_compare_fn_decl;
            call_def = FuncDef { func_body = Some (
              Expr.mk_app ~loc:f.field_loc ~typ:type_tp_expr (Expr.Var ra_valid_fn_qual_ident) [
                Expr.mk_app ~loc:f.field_loc ~typ:type_tp_expr (Expr.Var (QualIdent.from_ident heap_sub_chunk_fn_decl.call_decl_name)) [
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
      
      in
        
      let* _ = Rewriter.introduce_typecheck_symbol ~loc:f.field_loc ~f:Typing.process_symbol utils_module in

      Rewriter.return symbol

  | _ -> Rewriter.return symbol

  let introduce_heaps_in_stmts ~loc ~fields_list ~preds_list body : Stmt.t Rewriter.t =
    let open Rewriter.Syntax in
    (* TODO: Introduce variables of right types for predHeaps *)

    let* (heap_var_defs) = Rewriter.List.map fields_list ~f:(fun field_name -> 
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

      let _ = Ident.fresh loc (field_heap_name2 field_name).ident_name in

      let (heap_var_decl2: var_decl) = {
        var_name = field_heap_name2 field_name;
        var_loc = loc;
        var_type = Type.mk_map loc Type.ref field_elem_type;
        var_const = false;
        var_ghost = true;
        var_implicit = false;

        
      } in

      Rewriter.return Stmt.({ var_decl = heap_var_decl; var_init = None }, { var_decl = heap_var_decl2; var_init = None })
      
    ) in

    let* _ = Rewriter.List.iter heap_var_defs ~f:(fun (heap_var_decl, heap_var_decl2) -> 
      Logs.debug (fun m -> m "Rewrites.HeapsExplicitTrnsl.introduce_heaps_in_stmts: heap_var_decl: %a; heap_var_decl2: %a" Ident.pr heap_var_decl.var_decl.var_name Ident.pr heap_var_decl2.var_decl.var_name );
      let* _ = Rewriter.introduce_symbol (Module.VarDef heap_var_decl) in
      Rewriter.introduce_symbol (Module.VarDef heap_var_decl2)
    ) in

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

    let rec trnsl_inhale_expr (expr: expr) : Stmt.t Rewriter.t =
      trnsl_inhale_a [] expr
      

    and trnsl_inhale_a (conds: conditions) (expr: expr): Stmt.t Rewriter.t =
      let open Rewriter.Syntax in
  
      match expr with
      | App (Ite, [c; e1; e2], _) ->
        let* stmt1 = trnsl_inhale_a (c :: conds) e1 in
  
        let not_c = Expr.mk_not ~loc:(Expr.to_loc c) c in
        let* stmt2 = trnsl_inhale_a (not_c :: conds) e2 in
        
        Rewriter.return (Stmt.mk_block_stmt ~loc:(Expr.to_loc expr) [stmt1; stmt2])
      | App (Impl, [c; e2], _) ->
        trnsl_inhale_a (c :: conds) e2
  
      | App (And, e_list, _) ->
        let* stmts_list = Rewriter.List.map e_list ~f:(fun e -> trnsl_inhale_a conds e) in
        
        Rewriter.return (Stmt.mk_block_stmt ~loc:(Expr.to_loc expr) stmts_list)
        
  
      | _ -> trnsl_inhale_a2 {univ_vars = []; triggers = []} conds expr

    and trnsl_inhale_a2 (universal_quants: universal_quants) (conds: conditions) (expr: expr): Stmt.t Rewriter.t =
      let open Rewriter.Syntax in
  
      match expr with
      | App (And, e_list, _) ->
        let* stmts_list = Rewriter.List.map e_list ~f:(fun e -> trnsl_inhale_a2 universal_quants conds e) in
  
        Rewriter.return (Stmt.mk_block_stmt ~loc:(Expr.to_loc expr) stmts_list)
  
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
        let* stmt = trnsl_inhale_a2 universal_quants conds e in
  
        Rewriter.return stmt
  
      | _ -> trnsl_inhale_a2' universal_quants conds expr


    and trnsl_inhale_a2' (universal_quants: universal_quants) (conds: conditions) (expr: expr): Stmt.t Rewriter.t =
      let open Rewriter.Syntax in
  
      match expr with
      | App (And, e_list, _) ->
        let* stmts_list = Rewriter.List.map e_list ~f:(fun e -> trnsl_inhale_a2' universal_quants conds e) in

        Rewriter.return (Stmt.mk_block_stmt ~loc:(Expr.to_loc expr) stmts_list)
        
      | App (Impl, [c; e2], _) ->
        trnsl_inhale_a2' universal_quants (c :: conds) e2
      
      | App (Ite, [c; e1; e2], _) ->
        let* stmt1 = trnsl_inhale_a2' universal_quants (c :: conds) e1 in
  
        let not_c = Expr.mk_not ~loc:(Expr.to_loc c) c in
        let* stmt2 = trnsl_inhale_a2' universal_quants (not_c :: conds) e2 in
        
        Rewriter.return (Stmt.mk_block_stmt ~loc:(Expr.to_loc expr) [stmt1; stmt2])
  
      | _ -> trnsl_inhale_a0 universal_quants conds expr

      and trnsl_inhale_a0 (universal_quants: universal_quants) (conds: conditions) (expr: expr): Stmt.t Rewriter.t =
        let open Rewriter.Syntax in

        let univ_quants_list = universal_quants.univ_vars in
        (* creating list at the top to preserve order throughout *)

        match expr with
        | App (And, e_list, _) ->
          let* stmts_list = Rewriter.List.map e_list ~f:(fun e -> trnsl_inhale_a0 universal_quants conds e) in
            
          Rewriter.return (Stmt.mk_block_stmt ~loc:(Expr.to_loc expr) stmts_list)
  
    
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

          let havoc_stmt = Stmt.mk_havoc ~loc:(Expr.to_loc expr) field_heap2_qual_ident in
          let assume_stmt = 
            let l_var = Type.{ var_name = Ident.fresh (Expr.to_loc expr) "l"; var_loc = Expr.to_loc expr; 
            var_type = Type.ref; var_const = false; var_ghost = false; var_implicit = false; } in
  
            let l_expr = Expr.mk_var ~typ:l_var.var_type (QualIdent.from_ident l_var.var_name) in
            
            let univ_vars_list = List.map univ_quants_list ~f:(fun (var, var_decl) -> var_decl) in
  
            let l_eq_e1_expr = (Expr.mk_eq l_expr e1) in
            
            Stmt.mk_assume_expr ~loc:(Expr.to_loc expr) 
            (Expr.mk_binder ~loc:(Expr.to_loc expr) ~typ:Type.bool Forall [l_var] 
              (Expr.mk_binder ~loc:(Expr.to_loc expr) ~typ:Type.bool Forall univ_vars_list
                (Expr.mk_app ~loc:(Expr.to_loc expr) ~typ:Type.bool Expr.Ite [

                  (* m1(a,b,c) && l == f1(a, b, c) *)
                  Expr.mk_and ~loc:(Expr.to_loc expr) (l_eq_e1_expr :: conds);

                  (* field$Heap2[l] == field.comp( field$Heap[l], f2(a, b, c) ) *)
                  Expr.mk_eq ~loc:(Expr.to_loc expr) (Expr.mk_maplookup ~loc:(Expr.to_loc expr) field_heap2_expr l_expr)
                    (Expr.mk_app ~loc:(Expr.to_loc expr) ~typ:field_type 
                      (Expr.Var field_heapchunk_operator)  [
                        Expr.mk_maplookup ~loc:(Expr.to_loc expr) field_heap_expr l_expr;
                        e3;
                      ] );

              
                  (* field$Heap2[l] == field$Heap[l] *)
                  Expr.mk_eq ~loc:(Expr.to_loc expr) (Expr.mk_maplookup ~loc:(Expr.to_loc expr) field_heap2_expr l_expr) 
                    (Expr.mk_maplookup ~loc:(Expr.to_loc expr) field_heap_expr l_expr);
                ])
              )
            )
          in
  
          (* field$Heap := field$Heap2 *)
          let eq_stmt = Stmt.mk_assign ~loc:(Expr.to_loc expr) [field_heap_expr] field_heap2_expr in
          
          (* let* field_valid_fn = Rewriter.ProgUtils.get_field_utils_valid (Expr.to_loc expr) (Expr.to_qual_ident e2) in
          let heap_valid_stmt = Stmt.mk_assert_expr ~loc:(Expr.to_loc expr) 
            (Expr.mk_app ~loc:(Expr.to_loc expr) ~typ:Type.bool (Expr.Var field_valid_fn) [field_heap_expr])
  
          in *)

          let assume_heap_valid = Stmt.mk_assume_expr ~loc:(Expr.to_loc expr) 
            (Expr.mk_app ~loc:(Expr.to_loc expr) ~typ:Type.bool (Expr.Var field_heap_valid_fn) [field_heap_expr]) 
          
          in
  
          let* injectivity_assertion = generate_injectivity_assertions universal_quants conds e1 in

          let stmts_list = match univ_quants_list with
          | [] -> []
          | _ -> [injectivity_assertion]

          in

          let stmts_list = stmts_list @ [havoc_stmt; assume_stmt; eq_stmt; assume_heap_valid] in

          let stmt = Stmt.mk_block_stmt ~loc:(Expr.to_loc expr) stmts_list in
  
          Rewriter.return stmt
        end

        (* TODO: Add support for predicates *)

        | e ->
          let* is_e_pure = Rewriter.ProgUtils.is_expr_pure e in
          if is_e_pure then
            let body_expr = match conds with
            | [] -> e
            | _ -> Expr.mk_impl (Expr.mk_and conds) e 
          in
            let assume_expr = Expr.mk_binder ~loc:(Expr.to_loc e) ~typ:Type.bool ~trigs:(universal_quants.triggers) Forall (List.map univ_quants_list ~f:(fun (_, v_d) -> v_d)) body_expr in
            Rewriter.return (Stmt.mk_assume_expr ~loc:(Expr.to_loc e) assume_expr)
          else
           unsupported_expr_error expr
  end

  module TrnslExhale = struct
    let rec rewriter_eliminate_existentials_from_exhales (stmt: Stmt.t) : (Stmt.t, expr option) Rewriter.t_ext =
      let open Rewriter.Syntax in

      let rec find_existentials (expr: expr) : var_decl list =
        match expr with
        | Binder (Exists, var_decls, trgs, e, _) -> var_decls @ find_existentials e
        | Binder (_, var_decls, trgs, e, _) -> find_existentials e
        | App (_, exprs, _) -> List.concat_map exprs ~f:find_existentials

      in

      let elim_existentials_from_expr (expr: expr) (subst_map : expr qual_ident_map): expr = 
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


        let exhale_expr = spec.spec_form in
        begin
          match prev_expr with
          | None -> 
            Rewriter.return stmt
          
          | Some prev_expr ->
            let existential_vars = find_existentials exhale_expr in 
            
              match match_up_expr spec.spec_form prev_expr existential_vars with
              | None -> 
                Rewriter.return stmt

              | Some var_map ->
                let subst_map = Map.map var_map ~f:(fun (var_decl, expr) -> expr) in
                let subst_map = (Map.map_keys_exn (module QualIdent)) subst_map ~f:(fun ident -> QualIdent.from_ident ident) in
                let spec_form = elim_existentials_from_expr exhale_expr subst_map in

                let spec = { spec with spec_form } in

                Rewriter.return {stmt with stmt_desc = Basic (Spec (Exhale, spec))}
        end

      | Basic (Spec (Assert, spec)) ->
        let* () = Rewriter.set_user_state (Some spec.spec_form) in
        Rewriter.return stmt


      | _ -> 
        let* () = Rewriter.set_user_state None in
        Rewriter.Stmt.descend stmt ~f:rewriter_eliminate_existentials_from_exhales
    
    
    
    let rec trnsl_exhale_expr (expr: expr) : Stmt.t Rewriter.t =
      trnsl_exhale_a [] expr
      
    and trnsl_exhale_a (conds: conditions) (expr: expr): Stmt.t Rewriter.t =
      let open Rewriter.Syntax in
  
      match expr with
      | App (Ite, [c; e1; e2], _) ->
        let* stmt1 = trnsl_exhale_a (c :: conds) e1 in
  
        let not_c = Expr.mk_not ~loc:(Expr.to_loc c) c in
        let* stmt2 = trnsl_exhale_a (not_c :: conds) e2 in
        
        Rewriter.return (Stmt.mk_block_stmt ~loc:(Expr.to_loc expr) [stmt1; stmt2])
      | App (Impl, [c; e2], _) ->
        trnsl_exhale_a (c :: conds) e2
  
      | App (And, e_list, _) ->
        let* stmts_list = Rewriter.List.map e_list ~f:(fun e -> trnsl_exhale_a conds e) in
        
        Rewriter.return (Stmt.mk_block_stmt ~loc:(Expr.to_loc expr) stmts_list)
        
      | _ -> trnsl_exhale_a2 {univ_vars = []; triggers = []} conds expr

    and trnsl_exhale_a2 (universal_quants: universal_quants) (conds: conditions) (expr: expr): Stmt.t Rewriter.t =
      let open Rewriter.Syntax in
  
      match expr with
      | App (And, e_list, _) ->
        let* stmts_list = Rewriter.List.map e_list ~f:(fun e -> trnsl_exhale_a2 universal_quants conds e) in
  
        Rewriter.return (Stmt.mk_block_stmt ~loc:(Expr.to_loc expr) stmts_list)
  
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
        let* stmt = trnsl_exhale_a2 universal_quants conds e in
  
        Rewriter.return stmt
  
      | _ -> trnsl_exhale_a2' universal_quants conds expr


    and trnsl_exhale_a2' (universal_quants: universal_quants) (conds: conditions) (expr: expr): Stmt.t Rewriter.t =
      let open Rewriter.Syntax in
  
      match expr with
      | App (And, e_list, _) ->
        let* stmts_list = Rewriter.List.map e_list ~f:(fun e -> trnsl_exhale_a2' universal_quants conds e) in

        Rewriter.return (Stmt.mk_block_stmt ~loc:(Expr.to_loc expr) stmts_list)
        
      | App (Impl, [c; e2], _) ->
        trnsl_exhale_a2' universal_quants (c :: conds) e2
      
      | App (Ite, [c; e1; e2], _) ->
        let* stmt1 = trnsl_exhale_a2' universal_quants (c :: conds) e1 in
  
        let not_c = Expr.mk_not ~loc:(Expr.to_loc c) c in
        let* stmt2 = trnsl_exhale_a2' universal_quants (not_c :: conds) e2 in
        
        Rewriter.return (Stmt.mk_block_stmt ~loc:(Expr.to_loc expr) [stmt1; stmt2])
  
      | _ -> trnsl_exhale_a0 universal_quants conds expr

      and trnsl_exhale_a0 (universal_quants: universal_quants) (conds: conditions) (expr: expr): Stmt.t Rewriter.t =
        let open Rewriter.Syntax in

        let univ_quants_list = universal_quants.univ_vars in
        (* creating list at the top to preserve order throughout *)

        match expr with
        | App (And, e_list, _) ->
          let* stmts_list = Rewriter.List.map e_list ~f:(fun e -> trnsl_exhale_a0 universal_quants conds e) in

          Rewriter.return (Stmt.mk_block_stmt ~loc:(Expr.to_loc expr) stmts_list)  
    
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

          let havoc_stmt = Stmt.mk_havoc ~loc:(Expr.to_loc expr) field_heap2_qual_ident in
          let assume_stmt = 
            let l_var = Type.{ var_name = Ident.fresh (Expr.to_loc expr) "l"; var_loc = Expr.to_loc expr; 
            var_type = Type.ref; var_const = false; var_ghost = false; var_implicit = false; } in
  
            let l_expr = Expr.mk_var ~typ:l_var.var_type (QualIdent.from_ident l_var.var_name) in
            
            let univ_vars_list = List.map univ_quants_list ~f:(fun (var, var_decl) -> var_decl) in
  
            let l_eq_e1_expr = (Expr.mk_eq l_expr e1) in
            
            Stmt.mk_assume_expr ~loc:(Expr.to_loc expr) 
            (Expr.mk_binder ~loc:(Expr.to_loc expr) ~typ:Type.bool Forall [l_var] 
              (Expr.mk_binder ~loc:(Expr.to_loc expr) ~typ:Type.bool Forall univ_vars_list
                (Expr.mk_app ~loc:(Expr.to_loc expr) ~typ:Type.bool Expr.Ite [

                  (* m1(a,b,c) && l == f1(a, b, c) *)
                  Expr.mk_and ~loc:(Expr.to_loc expr) (l_eq_e1_expr :: conds);

                  (* field$Heap2[l] == field.comp( field$Heap[l], f2(a, b, c) ) *)
                  Expr.mk_eq ~loc:(Expr.to_loc expr) (Expr.mk_maplookup ~loc:(Expr.to_loc expr) field_heap2_expr l_expr)
                    (Expr.mk_app ~loc:(Expr.to_loc expr) ~typ:field_type 
                      (Expr.Var field_heapchunk_operator)  [
                        Expr.mk_maplookup ~loc:(Expr.to_loc expr) field_heap_expr l_expr;
                        e3;
                      ] );

              
                  (* field$Heap2[l] == field$Heap[l] *)
                  Expr.mk_eq ~loc:(Expr.to_loc expr) (Expr.mk_maplookup ~loc:(Expr.to_loc expr) field_heap2_expr l_expr) 
                    (Expr.mk_maplookup ~loc:(Expr.to_loc expr) field_heap_expr l_expr);
                ])
              )
            )
          in
  
          (* field$Heap := field$Heap2 *)
          let eq_stmt = Stmt.mk_assign ~loc:(Expr.to_loc expr) [field_heap_expr] field_heap2_expr in
          
          (* let* field_valid_fn = Rewriter.ProgUtils.get_field_utils_valid (Expr.to_loc expr) (Expr.to_qual_ident e2) in
          let heap_valid_stmt = Stmt.mk_assert_expr ~loc:(Expr.to_loc expr) 
            (Expr.mk_app ~loc:(Expr.to_loc expr) ~typ:Type.bool (Expr.Var field_valid_fn) [field_heap_expr])
  
          in *)

          let assert_heap_valid = Stmt.mk_assert_expr ~loc:(Expr.to_loc expr) 
            (Expr.mk_app ~loc:(Expr.to_loc expr) ~typ:Type.bool (Expr.Var field_heap_valid_fn) [field_heap_expr]) 
          
          in
  
          let* injectivity_assertion = generate_injectivity_assertions universal_quants conds e1 in

          let stmts_list = match univ_quants_list with
          | [] -> []
          | _ -> [injectivity_assertion]

          in

          let stmts_list = stmts_list @ [havoc_stmt; assume_stmt; eq_stmt; assert_heap_valid] in

          let stmt = Stmt.mk_block_stmt ~loc:(Expr.to_loc expr) stmts_list in
  
          Rewriter.return stmt
        end

        (* TODO: Add support for predicates *)

        | e ->
          let* is_e_pure = Rewriter.ProgUtils.is_expr_pure e in
          if is_e_pure then
            let assert_expr = Expr.mk_binder ~loc:(Expr.to_loc e) ~typ:Type.bool ~trigs:(universal_quants.triggers) Forall (List.map univ_quants_list ~f:(fun (_, v_d) -> v_d)) (Expr.mk_impl (Expr.mk_and conds) e) in

            let assert_stmt = (Stmt.mk_assert_expr ~loc:(Expr.to_loc e) assert_expr) in
            (* let assume_stmt = (Stmt.mk_assume_expr ~loc:(Expr.to_loc e) assert_expr) in *)
            (* Rewriter.return (Stmt.mk_block_stmt ~loc:(Expr.to_loc e) [assume_stmt; assert_stmt]) *)
            Rewriter.return assert_stmt
          else
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

          let* stmt = TrnslInhale.trnsl_inhale_expr expr in
          Rewriter.return stmt

        | Exhale ->
          let expr = spec.spec_form in

          let* stmt = TrnslExhale.trnsl_exhale_expr expr in
          Rewriter.return stmt
        | Assume -> 
          let* is_e_pure = Rewriter.ProgUtils.is_expr_pure spec.spec_form in
          if is_e_pure then
            Rewriter.return s
          else  
            Error.error s.stmt_loc "Assume statements with non-pure expressions are not supported."
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

            let* exhale_stmt = TrnslExhale.trnsl_exhale_expr spec.spec_form in
            let assume_false_stmt = Stmt.mk_assume_expr ~loc:s.stmt_loc (Expr.mk_bool false) in

            let cond_stmt = Stmt.Cond {
              cond_test = Expr.from_var_decl nondet_var; 
              cond_then = Stmt.mk_block_stmt ~loc:s.stmt_loc [exhale_stmt; assume_false_stmt];
              cond_else = Stmt.mk_block_stmt ~loc:s.stmt_loc []} in


            Rewriter.return Stmt.{stmt_desc = cond_stmt; stmt_loc = s.stmt_loc}
        end
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

    Logs.debug (fun m -> m "Rewrites.rewrite_introduce_heaps: Predicates mentioned in the body");

    let* body = HeapsExplicitTrnsl.introduce_heaps_in_stmts ~loc:c.call_decl.call_decl_loc ~fields_list ~preds_list body in

    let* body = HeapsExplicitTrnsl.rewrite_make_heaps_explicit body in

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
  
    | _ -> assert false
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

  Logs.debug (fun m1 -> m1 "Rewrites.all_rewrites: Starting rewrite_new_stmts on module %a" Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_stmts ~f:rewrite_new_stmts m in

  Logs.debug (fun m1 -> m1 "Rewrites.all_rewrites: Starting rewrite_fold_unfold_stmts on module %a" Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_stmts ~f:rewrite_fold_unfold_stmts m in

  Logs.debug (fun m1 -> m1 "Rewrites.all_rewrites: Starting rewrite_call_stmts on module %a" Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_stmts ~f:rewrite_call_stmts m in

  Logs.debug (fun m1 -> m1 "Rewrites.all_rewrites: Starting rewrite_ret_stmts on module %a" Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_stmts ~f:rewrite_ret_stmts m in

  Logs.debug (fun m1 -> m1 "Rewrites.all_rewrites: Starting rewrite_callable_pre_post_conds on module %a" Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_callables ~f:rewrite_callable_pre_post_conds m in

  Logs.debug (fun m1 -> m1 "Rewrites.all_rewrites: Starting rewrite_frac_field_types on module %a" Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rec_rewrite_symbols ~f:rewrite_frac_field_types m in
  
  Logs.debug (fun m1 -> m1 "Rewrites.all_rewrites: Starting rewrite_own_expr_4_arg on module %a" Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_expressions ~f:rewrite_own_expr_4_arg m in

  Logs.debug (fun m1 -> m1 "Rewrites.all_rewrites: Starting rewriter_skolemize_inhale_stmts on module %a" Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_stmts ~f:HeapsExplicitTrnsl.TrnslInhale.rewriter_skolemize_inhale_stmts m in

  Logs.debug (fun m1 -> m1 "Rewrites.all_rewrites: Starting rewriter_eliminate_existentials_from_exhales on module %a" Ident.pr m.mod_decl.mod_decl_name);
  let* m = 
    Rewriter.eval_with_user_state ~init:None
    (Rewriter.Module.rewrite_stmts ~f:HeapsExplicitTrnsl.TrnslInhale.rewriter_eliminate_binds_for_inhale m) in

  Logs.debug (fun m1 -> m1 "Rewrites.all_rewrites: Starting rewriter_eliminate_existentials_from_exhales on module %a" Ident.pr m.mod_decl.mod_decl_name);
  let* m = 
    Rewriter.eval_with_user_state ~init:None
    (Rewriter.Module.rewrite_stmts ~f:HeapsExplicitTrnsl.TrnslExhale.rewriter_eliminate_existentials_from_exhales m) in

  Logs.debug (fun m1 -> m1 "Rewrites.all_rewrites: Starting rewrite_add_field_utils on module %a" Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rec_rewrite_symbols ~f:HeapsExplicitTrnsl.rewrite_add_field_utils m in

  Logs.debug (fun m1 -> m1 "Rewrites.all_rewrites: Starting rewrite_introduce_heaps on module %a" Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_callables ~f:rewrite_introduce_heaps m in

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
