open Base
open Ast
open Util

let rec rewrite_compr_expr (expr: expr) : expr Rewriter.t =
  let open Rewriter.Syntax in
  match expr with
  | Binder (Compr, v_l, inner_expr, _expr_attr) ->
    let* _ = Rewriter.add_locals v_l
    and* inner_expr = rewrite_compr_expr inner_expr in
        
    let compr_fn_ident = Ident.fresh (Expr.to_loc expr) "compr" in

    let free_vars = Expr.fv inner_expr in
    
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
            Expr.mk_app ~typ:Type.bool Impl [
              inner_expr;
              
              Expr.mk_app ~typ:Type.bool Elem [ 
                Expr.from_var_decl var_decl;
                Expr.from_var_decl ret_var_decl
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
      call_decl_loc = Expr.to_loc expr;
    }
      
    in

    let compr_fn_qual_ident = QualIdent.from_ident compr_fn_ident in
    let compr_fn_def = Module.CallDef (Callable.{ call_decl; call_def = FuncDef { func_body = None;} }) in
    
    let new_expr = 
      Expr.mk_app ~typ:(ret_typ) ~loc:(Expr.to_loc expr) (Expr.Var compr_fn_qual_ident) actual_arg_exprs
    in

    let+ _ = Rewriter.introduce_symbol compr_fn_def in
    new_expr
      
  | _ -> Rewriter.Expr.descend expr ~f:rewrite_compr_expr

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
  
    let* loop_arg_var_decls, loop_arg_renaming_map, curr_loop_arg_var_decls = 
      begin
        (* Local variables accessed from loop body become arguments for loop procedure *)
        let curr_loop_args = Stmt.local_vars_accessed loop.loop_postbody |> Set.to_list in
        let+ curr_loop_arg_var_decls = Rewriter.List.map curr_loop_args ~f:(fun var -> 
          let+ symbol = Rewriter.find_and_reify stmt.stmt_loc (QualIdent.from_ident var) in
          
          (match symbol with
          | VarDef v -> v.var_decl
          | _ -> Error.error stmt.stmt_loc "Expected a variable")
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
        
        loop_arg_var_decls, loop_arg_renaming_map, curr_loop_arg_var_decls
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
          | _ -> Error.error stmt.stmt_loc "Expected a variable")
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
        call_decl_loc = stmt.stmt_loc;
      }
    in

    let loop_body =
      begin
        let set_ret_vals_to_initial_args = List.map (Map.to_alist loop_ret_renaming_map) ~f:(fun (old_var, new_expr) ->
          Stmt.mk_assign ~loc:(Stmt.loc stmt) [new_expr] (Map.find_exn loop_arg_renaming_map old_var)
        ) in

        let recurse_call =
          let lhs_list = List.map loop_ret_var_decls ~f:(fun var_decl -> QualIdent.from_ident var_decl.var_name) in

          let args_list = List.map loop_arg_var_decls ~f:(fun var_decl -> Expr.from_var_decl var_decl) in

          Stmt.mk_call ~loc:(Stmt.loc stmt) ~lhs:lhs_list (QualIdent.from_ident loop_proc_name) args_list in

        (* TODO: Rename variables from curr_vars to loop_vars in loop body *)
        let loop_body = loop.loop_postbody in

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

        Stmt.mk_block_stmt ~loc:stmt.stmt_loc (set_ret_vals_to_initial_args @ [cond_stmt; ret_stmt])
      end
    in

    let loop_proc_symbol =
      let call_def = Callable.{ call_decl = new_proc_decl; call_def = ProcDef { proc_body = Some loop_body; } } in
      Module.CallDef call_def

    in

    let* _ = Rewriter.introduce_symbol loop_proc_symbol in

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

      let+ symbol = Rewriter.find_and_reify stmt.stmt_loc curr_proc_name in
          
      (match symbol with
      | CallDef c -> c.call_decl
      | _ -> Error.error stmt.stmt_loc "Expected a call_def")
    
    in

    let postconds_spec = callable_decl.call_decl_postcond in

    let postconds_assert_stmts = List.map postconds_spec ~f:(fun spec -> Stmt.mk_assert_spec ~loc:stmt.stmt_loc spec) in

    let assume_false = Stmt.mk_assume_expr ~loc:stmt.stmt_loc (Expr.mk_bool ~loc:stmt.stmt_loc false) in

    let new_stmt = Stmt.mk_block_stmt ~loc:stmt.stmt_loc (postconds_assert_stmts @ [assume_false]) in

    Rewriter.return new_stmt


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
      | _ -> Error.error stmt.stmt_loc "Expected a variable"
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

      let frac_type = Type.mk_var f.field_loc (QualIdent.append frac_mod_name (Ident.make f.field_loc "T" 0)) in

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

  | Binder (_, _, expr, _) ->
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

  type universal_quants = (ident * var_decl) list

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
        let var_decls_forall = (List.map universal_quants ~f:(fun (var, var_decl) -> var_decl)) in
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
    let open Rewriter.Syntax in

    (* Running example : 
        Say we have:
        forall a, b :: p1(a, b) && p2(a, b) ==> f(a, b) 

        universal_quants : { a, b }
        conditions : [ p1(a, b); p2(a, b) ]
        expr : f(a, b)

    
    *)

    let univ_quants_list = universal_quants in
  
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

  let introduce_heaps_in_stmts ~loc ~fields_list ~preds_list body : Stmt.t Rewriter.t =
    let open Rewriter.Syntax in
    (* TODO: Introduce variables of right types for predHeaps *)

    let* (heap_var_defs) = Rewriter.List.map fields_list ~f:(fun field_name -> 
      let* field_symbol = Rewriter.find_and_reify (Loc.dummy) field_name in

      let field_type = match field_symbol with
        | FieldDef f -> f.field_type
        | _ -> Error.error (Loc.dummy) "Expected a field_def"

      in

      let (heap_var_decl: var_decl) = {
        var_name = field_heap_name field_name;
        var_loc = loc;
        var_type = Type.mk_map loc Type.ref field_type;
        var_const = false;
        var_ghost = true;
        var_implicit = false;

        
      } in

      let (heap_var_decl2: var_decl) = {
        var_name = field_heap_name2 field_name;
        var_loc = loc;
        var_type = Type.mk_map loc Type.ref field_type;
        var_const = false;
        var_ghost = true;
        var_implicit = false;

        
      } in

      Rewriter.return Stmt.({ var_decl = heap_var_decl; var_init = None }, { var_decl = heap_var_decl2; var_init = None })
      
    ) in

    let* _ = Rewriter.List.iter heap_var_defs ~f:(fun (heap_var_decl, heap_var_decl2) -> 
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
    | Binder (Compr, v_d1, e1, _), Binder (Compr, v_d2, e2, _)
    | Binder (Forall, v_d1, e1, _), Binder (Forall, v_d2, e2, _) ->
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

    | Binder (Exists, v_d1, e1, _), e2 ->
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
        let univ_quants_list = universal_quants in
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
      | Binder (Forall, var_decls, e, e_attr) ->
        let universal_quants = 
          let new_quants = List.map var_decls ~f:(fun var_decl -> (var_decl.var_name, var_decl)) in
           universal_quants @ new_quants 
        in
          
          (* List.fold var_decls ~init:universal_quants ~f:(fun map var_decl -> 
          Map.add_exn map ~key:var_decl.var_name ~data:var_decl
        in *)
        let* e = skolemize_inhale_expr universal_quants subst e in

        Rewriter.return Expr.(Binder (Forall, var_decls, e, e_attr))

      | Binder (Exists, var_decls, e, e_attr) ->
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
          let* e = skolemize_inhale_expr [] (Map.empty (module QualIdent)) spec.spec_form in

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
      let open Rewriter.Syntax in

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
        
  
      | _ -> trnsl_inhale_a2 [] conds expr

    and trnsl_inhale_a2 (universal_quants: universal_quants) (conds: conditions) (expr: expr): Stmt.t Rewriter.t =
      let open Rewriter.Syntax in
  
      match expr with
      | App (And, e_list, _) ->
        let* stmts_list = Rewriter.List.map e_list ~f:(fun e -> trnsl_inhale_a2 universal_quants conds e) in
  
        Rewriter.return (Stmt.mk_block_stmt ~loc:(Expr.to_loc expr) stmts_list)
  
      | Binder (Forall, var_decls, e, _) ->
        let universal_quants = 
          let new_quants = List.map var_decls ~f:(fun var_decl -> (var_decl.var_name, var_decl)) in
           universal_quants @ new_quants 
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

        let univ_quants_list = universal_quants in
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
          let assert_stmt = 
            let l_var = Type.{ var_name = Ident.fresh (Expr.to_loc expr) "l"; var_loc = Expr.to_loc expr; 
            var_type = Type.ref; var_const = false; var_ghost = false; var_implicit = false; } in
  
            let l_expr = Expr.mk_var ~typ:l_var.var_type (QualIdent.from_ident l_var.var_name) in
            
            let univ_vars_list = List.map univ_quants_list ~f:(fun (var, var_decl) -> var_decl) in
  
            let l_eq_e1_expr = (Expr.mk_eq l_expr e1) in
            
            Stmt.mk_assert_expr ~loc:(Expr.to_loc expr) 
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

          let assume_heap_valid = Stmt.mk_assert_expr ~loc:(Expr.to_loc expr) 
            (Expr.mk_app ~loc:(Expr.to_loc expr) ~typ:Type.bool (Expr.Var field_heap_valid_fn) [field_heap_expr]) 
          
          in
  
          let* injectivity_assertion = generate_injectivity_assertions universal_quants conds e1 in

          let stmts_list = match univ_quants_list with
          | [] -> []
          | _ -> [injectivity_assertion]

          in

          let stmts_list = stmts_list @ [havoc_stmt; assert_stmt; eq_stmt; assume_heap_valid] in

          let stmt = Stmt.mk_block_stmt ~loc:(Expr.to_loc expr) stmts_list in
  
          Rewriter.return stmt
        end

        (* TODO: Add support for predicates *)

        | e ->
          let* is_e_pure = Rewriter.ProgUtils.is_expr_pure e in
          if is_e_pure then
            let assume_expr = Expr.mk_binder ~loc:(Expr.to_loc e) ~typ:Type.bool Forall (List.map univ_quants_list ~f:(fun (_, v_d) -> v_d)) (Expr.mk_impl (Expr.mk_and conds) e) in
            Rewriter.return (Stmt.mk_assume_expr ~loc:(Expr.to_loc e) assume_expr)
          else
           unsupported_expr_error expr
  end

  module TrnslExhale = struct
    let rec rewriter_eliminate_existentials_from_exhales (stmt: Stmt.t) : (Stmt.t, expr option) Rewriter.t_ext =
      let open Rewriter.Syntax in

      let rec find_existentials (expr: expr) : var_decl list =
        match expr with
        | Binder (Exists, var_decls, e, _) -> var_decls @ find_existentials e
        | Binder (_, var_decls, e, _) -> find_existentials e
        | App (_, exprs, _) -> List.concat_map exprs ~f:find_existentials

      in

      let elim_existentials_from_expr (expr: expr) (subst_map : expr qual_ident_map): expr = 
        let rec elim_exists (expr: expr) (subst_map) : expr = 
          match expr with
          | Binder (Exists, var_decls, e, _) ->
            let all_existentials_exist = List.for_all var_decls ~f:(fun var_decl -> 
              Map.mem subst_map (QualIdent.from_ident var_decl.var_name)
            ) in

            if not all_existentials_exist then
              Error.internal_error (Expr.to_loc expr) "Expected all existentials to be matched up"
            else
              e

          | Binder (b, var_decls, e, expr_attr) ->
              let e = elim_exists e subst_map in
              Binder (b, var_decls, e, expr_attr)

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
      let open Rewriter.Syntax in

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
        
      | _ -> trnsl_exhale_a2 [] conds expr

    and trnsl_exhale_a2 (universal_quants: universal_quants) (conds: conditions) (expr: expr): Stmt.t Rewriter.t =
      let open Rewriter.Syntax in
  
      match expr with
      | App (And, e_list, _) ->
        let* stmts_list = Rewriter.List.map e_list ~f:(fun e -> trnsl_exhale_a2 universal_quants conds e) in
  
        Rewriter.return (Stmt.mk_block_stmt ~loc:(Expr.to_loc expr) stmts_list)
  
      | Binder (Forall, var_decls, e, _) ->
        let universal_quants = 
          let new_quants = List.map var_decls ~f:(fun var_decl -> (var_decl.var_name, var_decl)) in
          universal_quants @ new_quants 
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

        let univ_quants_list = universal_quants in
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
          let assert_stmt = 
            let l_var = Type.{ var_name = Ident.fresh (Expr.to_loc expr) "l"; var_loc = Expr.to_loc expr; 
            var_type = Type.ref; var_const = false; var_ghost = false; var_implicit = false; } in
  
            let l_expr = Expr.mk_var ~typ:l_var.var_type (QualIdent.from_ident l_var.var_name) in
            
            let univ_vars_list = List.map univ_quants_list ~f:(fun (var, var_decl) -> var_decl) in
  
            let l_eq_e1_expr = (Expr.mk_eq l_expr e1) in
            
            Stmt.mk_assert_expr ~loc:(Expr.to_loc expr) 
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

          let stmts_list = stmts_list @ [havoc_stmt; assert_stmt; eq_stmt; assert_heap_valid] in

          let stmt = Stmt.mk_block_stmt ~loc:(Expr.to_loc expr) stmts_list in
  
          Rewriter.return stmt
        end

        (* TODO: Add support for predicates *)

        | e ->
          let* is_e_pure = Rewriter.ProgUtils.is_expr_pure e in
          if is_e_pure then
            let assume_expr = Expr.mk_binder ~loc:(Expr.to_loc e) ~typ:Type.bool Forall (List.map univ_quants_list ~f:(fun (_, v_d) -> v_d)) (Expr.mk_impl (Expr.mk_and conds) e) in
            Rewriter.return (Stmt.mk_assume_expr ~loc:(Expr.to_loc e) assume_expr)
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
            let assume_stmt = Stmt.mk_assume_expr ~loc:s.stmt_loc spec.spec_form in
            Rewriter.return (Stmt.mk_block_stmt ~loc:s.stmt_loc [s; assume_stmt])
          else
            let nondet_var = Type.{ var_name = Ident.fresh s.stmt_loc "$nondet"; var_loc = s.stmt_loc; 
              var_type = Type.bool; var_const = true; var_ghost = false; var_implicit = false; } in

            let (nondet_var_def: Module.symbol) = VarDef {var_decl = nondet_var; var_init = None} in

            let* _ = Rewriter.introduce_symbol nondet_var_def in

            let* exhale_stmt = TrnslExhale.trnsl_exhale_expr spec.spec_form in
            let assert_false_stmt = Stmt.mk_assert_expr ~loc:s.stmt_loc (Expr.mk_bool false) in

            let cond_stmt = Stmt.Cond {
              cond_test = Expr.from_var_decl nondet_var; 
              cond_then = Stmt.mk_block_stmt ~loc:s.stmt_loc [exhale_stmt; assert_false_stmt];
              cond_else = Stmt.mk_block_stmt ~loc:s.stmt_loc []} in


            Rewriter.return Stmt.{stmt_desc = cond_stmt; stmt_loc = s.stmt_loc}
        end
      | _ -> Rewriter.return s
      end 
    | _ -> 
      let* s = Rewriter.Stmt.descend s ~f:rewrite_make_heaps_explicit in
  
      Rewriter.return s

  (* and trnsl_a (inhale_exhale: inhale_exhale) ((conds1, conds2): conditionals) (expr: expr): (Stmt.t list) Rewriter.t =
    let open Rewriter.Syntax in
    assert (List.is_empty conds2);

    match expr with
    | App (Ite, [c; e1; e2], _) ->
      let* stmts1 = trnsl_a inhale_exhale (c :: conds1, conds2) e1 in

      let not_c = Expr.mk_not ~loc:(Expr.to_loc c) c in
      let* stmts2 = trnsl_a inhale_exhale (not_c :: conds1, conds2) e2 in
      
      Rewriter.return (stmts1 @ stmts2)
    | App (Impl, [c; e2], _) ->
      trnsl_a inhale_exhale (c :: conds1, conds2) e2

    | App (And, e_list, _) ->
      let* stmts_list_list = Rewriter.List.map e_list ~f:(fun e -> trnsl_a inhale_exhale (conds1, conds2) e) in
      
      stmts_list_list |> List.concat |> Rewriter.return

    | _ -> trnsl_a2 inhale_exhale (Map.empty (module Ident)) (conds1, conds2) expr

  and trnsl_a2 (inhale_exhale: inhale_exhale) (universal_quants: universal_quants) ((conds1, conds2): conditionals) (expr: expr): (Stmt.t list) Rewriter.t =
    let open Rewriter.Syntax in
    assert (List.is_empty conds2);

    match expr with
    | App (And, e_list, _) ->
      let* stmts_list_list = Rewriter.List.map e_list ~f:(fun e -> trnsl_a2 inhale_exhale universal_quants (conds1, conds2) e) in

      stmts_list_list |> List.concat |> Rewriter.return

    | Binder (Forall, var_decls, e, _) ->
      let universal_quants = List.fold var_decls ~init:universal_quants ~f:(fun map var_decl -> 
        Map.add_exn map ~key:var_decl.var_name ~data:var_decl
      ) in
      let* stmts = trnsl_a2 inhale_exhale universal_quants (conds1, conds2) e in

      Rewriter.return stmts

    | _ -> trnsl_a2' inhale_exhale universal_quants (conds1, conds2) expr

  and trnsl_a2' (inhale_exhale: inhale_exhale) (universal_quants: universal_quants) ((conds1, conds2): conditionals) (expr: expr): (Stmt.t list) Rewriter.t =
    let open Rewriter.Syntax in
    assert (List.is_empty conds2);

    match expr with
    | App (And, e_list, _) ->
      let* stmts_list_list = Rewriter.List.map e_list ~f:(fun e -> trnsl_a2' inhale_exhale universal_quants (conds1, conds2) e) in
      
      stmts_list_list |> List.concat |> Rewriter.return
    | App (Impl, [c; e2], _) ->
      trnsl_a2' inhale_exhale universal_quants (c :: conds1, conds2) e2
    
    | App (Ite, [c; e1; e2], _) ->
      let* stmts1 = trnsl_a2' inhale_exhale universal_quants (c :: conds1, conds2) e1 in

      let not_c = Expr.mk_not ~loc:(Expr.to_loc c) c in
      let* stmts2 = trnsl_a2' inhale_exhale universal_quants (not_c :: conds1, conds2) e2 in
      
      Rewriter.return (stmts1 @ stmts2)

    | _ -> trnsl_a1 inhale_exhale universal_quants (conds1, conds2) (Map.empty (module Ident)) expr

  and trnsl_a1 (inhale_exhale: inhale_exhale) (universal_quants: universal_quants) ((conds1, conds2): conditionals) (existential_quants: existential_quants) (expr: expr): (Stmt.t list) Rewriter.t =
    let open Rewriter.Syntax in
    assert (List.is_empty conds2);

    match expr with
    | App (And, e_list, _) ->
      let* stmts_list_list = Rewriter.List.map e_list ~f:(fun e -> trnsl_a1 inhale_exhale universal_quants (conds1, conds2) existential_quants e) in
      
      stmts_list_list |> List.concat |> Rewriter.return

    | Binder (Exists, var_decls, e, _) ->
      let existential_quants = List.fold var_decls ~init:existential_quants ~f:(fun map var_decl -> 
        let quantified_exprs = [] 
        in
        Map.add_exn map ~key:var_decl.var_name ~data:{ var_decl; quantified_exprs; }
      ) in

      let* stmts = trnsl_a1 inhale_exhale universal_quants (conds1, conds2) existential_quants e in

      Rewriter.return stmts

    | _ -> 
      
      let* existential_quants, stmts = trnsl_a1' inhale_exhale universal_quants (conds1, conds2) existential_quants expr in

      (* TODO: Add extra stmts binding existentials over multiple heapchunks *)

      Rewriter.return stmts
  
  and trnsl_a1' (inhale_exhale: inhale_exhale) (universal_quants: universal_quants) ((conds1, conds2): conditionals) (existential_quants: existential_quants) (expr: expr): (existential_quants * Stmt.t list ) Rewriter.t =
    let open Rewriter.Syntax in
    match expr with
    | App (And, e_list, _) ->
      let* (existential_quants, stmts_list_list) = Rewriter.List.fold_map e_list ~init:existential_quants ~f:(fun existential_quants expr -> 
        let* existential_quants, stmts = trnsl_a1' inhale_exhale universal_quants (conds1, conds2) existential_quants expr in
        Rewriter.return (existential_quants, stmts)  
      ) in

      let stmts_list = List.concat stmts_list_list in

      Rewriter.return (existential_quants, stmts_list)

    | App (Impl, [c; e2], _) ->
      trnsl_a1' inhale_exhale universal_quants (conds1, c :: conds2) existential_quants e2

    | App (Ite, [c; e1; e2], _) ->
      let* existential_quants, stmts1 = trnsl_a1' inhale_exhale universal_quants (conds1, c :: conds2) existential_quants e1 in

      let not_c = Expr.mk_not ~loc:(Expr.to_loc c) c in
      let* existential_quants, stmts2 = trnsl_a1' inhale_exhale universal_quants (conds1, not_c :: conds2) existential_quants e2 in
      
      Rewriter.return (existential_quants, (stmts1 @ stmts2))

    | _ -> trnsl_a0 inhale_exhale universal_quants (conds1, conds2) existential_quants expr


  and trnsl_a0 (inhale_exhale: inhale_exhale) (universal_quants: universal_quants) ((conds1, conds2) as conditionals: conditionals) (existential_quants: existential_quants) (expr: expr): (existential_quants * Stmt.t list) Rewriter.t =
    let open Rewriter.Syntax in
    match expr with
    | App (And, e_list, _) ->
      let* (existential_quants, stmts_list_list) = Rewriter.List.fold_map e_list ~init:existential_quants ~f:(fun existential_quants expr -> 
        let* existential_quants, stmts = trnsl_a0 inhale_exhale universal_quants (conds1, conds2) existential_quants expr in
        Rewriter.return (existential_quants, stmts)  
      ) in 

      let stmts_list = List.concat stmts_list_list in

      Rewriter.return (existential_quants, stmts_list)
        


      (* let* stmts_list_list = Rewriter.List.map e_list ~f:(fun e -> trnsl_a0 inhale_exhale universal_quants (conds1, conds2) existential_quants e) in
      
      stmts_list_list |> List.concat |> Rewriter.return *)

    | App (Own, [e1; e2; e3], _) ->

      (* forall a, b, c :: m1(a, b, c) ==> exists d, e, f :: m2(a, b, c, d, e, f) ==> own(f1(a, b, c), field, f2(a, b, c, d, e, f))

      ===>

      // asserting injectivity of functions
      assert forall a, b, c, a', b', c' :: m1(a, b, c) && m1(a', b', c') ==> forall d, e, f :: m2(a, b, c, d, e, f) ==> f1(a, b, c) == f1(a', b', c') ==>    (a == a' && b == b' && c == c')

      assert forall a, b, c :: m1(a, b, c) ==> forall d, e, f, d', e', f' :: m2(a, b, c, d, e, f) && m2(a, b, c, d', e', f') ==> f2(a, b, c, d, e, f) == f2(a, b, c, d', e', f') ==> (d == d' && e == e' && f == f')



      f2$inv_d(v) returns ret 
      ensures forall a, b, c, d, e, f :: m1(a,b,c) && m2(a, b, c, d, e, f) && v == f2(a, b, c, d, e, f) ==> d == ret

      Introduce_symbol f2$inv_d(v)


      f2$inv_e(v) returns ret
      ensures forall a, b, c, d, e, f :: m1(a,b,c) && m2(a, b, c, d, e, f) && v == f2(a, b, c, d, e, f) ==> e == ret

      Introduce_symbol f2$inv_e(v)

      f2$inv_f(v) returns ret
      ensures forall a, b, c, d, e, f :: m1(a,b,c) && m2(a, b, c, d, e, f) && v == f2(a, b, c, d, e, f) ==> f == ret

      Introduce_symbol f2$inv_f(v)

      havoc(field$Heap2);

      assert forall l: Ref :: 
        exists a, b, c, d, e, f :: m1(a,b,c) && m2(a, b, c, d, e, f) && l == f1(a, b, c) ?
          exists a, b, c, d, e, f :: 
              m1(a,b,c) && m2(a, b, c, d, e, f) && 
              l == f1(a, b, c) && 
              field$Heap2[l] == field.comp( field$Heap[l], f2(a, b, c, d, e, f) ) :
          field$Heap2[l] == field$Heap[l]

      field$Heap := field$Heap2
      
      d : m2(a, b, c, d, e, f) ==> f2$inv_d(field$Heap[f1(a, b, c)])
      e : m2(a, b, c, d, e, f) ==> f2$inv_e(field$Heap[f1(a, b, c)])
      f : m2(a, b, c, d, e, f) ==> f2$inv_f(field$Heap[f1(a, b, c)])
      
      *)

      let field_heap_name = field_heap_name (Expr.to_qual_ident e2) in
      let field_heap_qual_ident = QualIdent.from_ident field_heap_name in
      let field_heap_expr = Expr.mk_var field_heap_qual_ident in

      let field_heap2_name = field_heap_name2 (Expr.to_qual_ident e2) in
      let field_heap2_qual_ident = QualIdent.from_ident field_heap2_name in
      let field_heap2_expr = Expr.mk_var field_heap2_qual_ident in

      let field_type = match Expr.to_type e2 with
        | App (Fld, [tp_expr], _) -> tp_expr
        | _ -> Error.type_error (Expr.to_loc e2) "Expected field identifier."

      in

      let* (field_heapchunk_operator: qual_ident) = 
        let field_name = (Expr.to_qual_ident e2) in

        match inhale_exhale with
        | Inhale -> Rewriter.ProgUtils.get_field_utils_comp (Expr.to_loc e2) field_name
        | Exhale -> Rewriter.ProgUtils.get_field_utils_frame (Expr.to_loc e2) field_name
      in

      let location_local_vars = Expr.expr_local_accesses e1 in

      if List.exists (Map.keys existential_quants) ~f:(fun var -> List.mem location_local_vars var ~equal:Ident.equal) then
        Error.error (Expr.to_loc expr) "Existential quantified variable used in location of own expression."

      else begin
        let* injectivity_assertions1 = generate_injectivity_assertions universal_quants conditionals existential_quants e1 in

        let* injectivity_assertions2 = generate_injectivity_assertions universal_quants conditionals existential_quants e2 in

        let* existential_quants_list = Rewriter.List.map (Map.to_alist existential_quants) ~f:(fun (var, { var_decl; quantified_exprs }) -> 
          let* inv_fn_qual_ident = generate_inv_function universal_quants conditionals existential_quants e3 var in

          let inv_expr = Expr.mk_app ~loc:(Expr.to_loc expr) ~typ:var_decl.var_type 
            (Expr.Var inv_fn_qual_ident) 
              [ 
                Expr.mk_maplookup ~loc:(Expr.to_loc expr) field_heap_expr e1;
              ] in


          let quantified_exprs = (inv_expr, (conds1, conds2)) :: quantified_exprs in
          Rewriter.return (var, { var_decl; quantified_exprs; })
        ) in 

        let existential_quants = (Map.of_alist_exn (module Ident)) existential_quants_list in

        
        let havoc_stmt = Stmt.mk_havoc ~loc:(Expr.to_loc expr) field_heap2_qual_ident in
        let assert_stmt = 
          let l_var = Type.{ var_name = Ident.fresh (Expr.to_loc expr) "l"; var_loc = Expr.to_loc expr; 
          var_type = Type.ref; var_const = false; var_ghost = false; var_implicit = false; } in

          let l_expr = Expr.mk_var (QualIdent.from_ident l_var.var_name) in
          
          let univ_vars_list = List.map (Map.to_alist universal_quants) ~f:(fun (var, var_decl) -> var_decl) in
          let existential_vars_list =  List.map (Map.to_alist existential_quants) ~f:(fun (var, { var_decl; _ }) -> var_decl) in

          let l_eq_e1_expr = (Expr.mk_eq l_expr e1) in
          
          Stmt.mk_assert_expr ~loc:(Expr.to_loc expr) 
          (Expr.mk_binder ~loc:(Expr.to_loc expr) ~typ:Type.bool Forall [l_var] 
            (Expr.mk_app ~loc:(Expr.to_loc expr) ~typ:Type.bool Expr.Ite 
            [
            (* if: *)
              (* l == f1(a, b, c) && m1(a, b, c) && m2(a,b,c,d,e,f) *)
              Expr.mk_binder ~loc:(Expr.to_loc expr) ~typ:Type.bool Exists (univ_vars_list @ existential_vars_list) 
                (Expr.mk_and (l_eq_e1_expr :: conds1 @ conds2));



            (* then: *)
              (* exists a, b, c, d, e, f :: 
                field$Heap2[l] == field.comp( field$Heap[l], f2(a, b, c, d, e, f) ) &&
                l == f1(a, b, c) &&
                m1(a,b,c) && m2(a, b, c, d, e, f)
              *)
              Expr.mk_binder ~loc:(Expr.to_loc expr) ~typ:Type.bool Exists (univ_vars_list @ existential_vars_list) 
              (Expr.mk_and (  
                (* field$Heap2[l] == field.comp( field$Heap[l], f2(a, b, c, d, e, f) *)
                Expr.mk_eq 
                  (Expr.mk_maplookup ~loc:(Expr.to_loc expr) field_heap2_expr l_expr)
                  (Expr.mk_app ~loc:(Expr.to_loc expr) ~typ:field_type 
                    (Expr.Var field_heapchunk_operator)  [
                      Expr.mk_maplookup ~loc:(Expr.to_loc expr) field_heap_expr l_expr;
                      e3;
                    ] )

                ::  l_eq_e1_expr :: conds1 @ conds2));

            (* else: *)
              Expr.mk_eq (Expr.mk_maplookup ~loc:(Expr.to_loc expr) field_heap2_expr l_expr) 
                (Expr.mk_maplookup ~loc:(Expr.to_loc expr) field_heap_expr l_expr);

            ])
          )
        
        in

        (* field$Heap := field$Heap2 *)
        let eq_stmt = Stmt.mk_assign ~loc:(Expr.to_loc expr) [field_heap_expr] field_heap2_expr in
        
        let* field_valid_fn = Rewriter.ProgUtils.get_field_utils_valid (Expr.to_loc expr) (Expr.to_qual_ident e2) in
        let heap_valid_stmt = Stmt.mk_assert_expr ~loc:(Expr.to_loc expr) 
          (Expr.mk_app ~loc:(Expr.to_loc expr) ~typ:Type.bool (Expr.Var field_valid_fn) [field_heap_expr])

        in

        let stmts = match inhale_exhale with
          | Inhale -> [havoc_stmt; assert_stmt; eq_stmt]  
          | Exhale -> [havoc_stmt; assert_stmt; eq_stmt; heap_valid_stmt]
        
        in

        Rewriter.return (existential_quants, stmts)
      end


    (* TODO: Handle pure expressions *)
    | _ -> 
       unsupported_expr_error expr *)

end



let rewrite_introduce_heaps (c: Callable.t) : Callable.t Rewriter.t =
  let open Rewriter.Syntax in
  match c.call_def with
  | FuncDef _ -> 
    Rewriter.return c

  | ProcDef {proc_body = None} ->
    Rewriter.return c
  
  | ProcDef {proc_body = Some body} -> 
    let* preds_list = stmt_preds_mentioned body in
    let fields_list = Stmt.stmt_fields_accessed body in

    let* body = HeapsExplicitTrnsl.introduce_heaps_in_stmts ~loc:c.call_decl.call_decl_loc ~fields_list ~preds_list body in

    let* body = HeapsExplicitTrnsl.rewrite_make_heaps_explicit body in

    Rewriter.return { c with call_def = ProcDef { proc_body = Some body; } }
  
(* let rewrite_add_field_utils (symbol: Module.symbol) : Module.symbol Rewriter.t =
  let open Rewriter.Syntax in
  match symbol with
  | FieldDef f ->
    let utils_module = 
      (* 
      module f$utils {
        type T = f.field_type.T;
        func f$heapValid(h: Map[Ref, T]) returns (ret:Bool) {
          forall l: Ref :: T.valid(h[l])
        }

        func f$heapAddChunk(x1: T, x2: T) returns (ret: T) {
          T.comp(x1, x2)
        }

        func f$heapSubChunk(x1: T, x2: T) returns (ret: T) {
          T.frame(x1, x2)
        }

        func f$heapchunk_compare(x1: T, x2: T) returns (ret: Bool) {
          T.valid(f$heapSubChunk(x1, x2))
        }
      }
       *)

      (* let* curr_scope = Rewriter.current_scope in
      let* curr_tbl = Rewriter.get_table in *)
      (* let field_fully_qual_name = SymbolTbl.fully_qualify f.field_name curr_scope curr_tbl in *)

      let* field_fully_qual_name = Rewriter.resolve f.field_loc (QualIdent.from_ident f.field_name) in

      let mod_decl =
        let mod_name = ProgUtils.serialize (QualIdent.to_stringfield_fully_qual_name) in
        let mod_decl_formals = [] in
        let mod_decl_returns = None in
        let mod_decl_interfaces = Set.empty (module QualIdent) in
        let mod_decl_rep = None in
        let mod_decl_is_ra = false in
        let mod_decl_is_interface = false in
        let mod_decl_loc = f.field_loc in

        { 
          Module.mod_name; 
          mod_decl_formals; 
          mod_decl_returns; 
          mod_decl_interfaces; 
          mod_decl_rep; 
          mod_decl_is_ra; 
          mod_decl_is_interface; 
          mod_decl_loc; 
        }
      in

      let mod_def =
        ()
      in
      
      ()
    
    in

    ()
  | _ -> Rewriter.return symbol *)
    

(* let rewrite_ssa_transform  (c: Callable.t) : Callable.t Rewriter.t =
    () *)



let rec all_rewrites (m: Module.t) : Module.t Rewriter.t =
  let open Rewriter.Syntax in
  let* m = Rewriter.Module.rewrite_symbols ~f:rewrite_frac_field_types m in
  let* m = Rewriter.Module.rewrite_expressions ~f:rewrite_own_expr_4_arg m in
  let* m = Rewriter.Module.rewrite_expressions ~f:rewrite_compr_expr m in
  let* m = Rewriter.Module.rewrite_stmts ~f:rewrite_loops m in
  let* m = Rewriter.Module.rewrite_stmts ~f:rewrite_ret_stmts m in
  let* m = Rewriter.Module.rewrite_stmts ~f:rewrite_fold_unfold_stmts m in
  let* m = Rewriter.Module.rewrite_stmts ~f:rewrite_call_stmts m in

  let* m = Rewriter.Module.rewrite_stmts ~f:HeapsExplicitTrnsl.TrnslInhale.rewriter_skolemize_inhale_stmts m in

  let* m = 
    Rewriter.eval_with_user_state ~init:None
    (Rewriter.Module.rewrite_stmts ~f:HeapsExplicitTrnsl.TrnslInhale.rewriter_eliminate_binds_for_inhale m) in

  let* m = 
    Rewriter.eval_with_user_state ~init:None
    (Rewriter.Module.rewrite_stmts ~f:HeapsExplicitTrnsl.TrnslExhale.rewriter_eliminate_existentials_from_exhales m) in

  let* m = Rewriter.Module.rewrite_stmts ~f:HeapsExplicitTrnsl.rewrite_make_heaps_explicit m in

  (* TODO: havoc return vars before inhaling *)

  Rewriter.return m



let process_module ?(tbl = SymbolTbl.create ()) (m: Module.t) = 
  assert (SymbolTbl.curr_is_root tbl);
  (* assert Ident.(m.mod_decl.mod_decl_name = QualIdent.to_ident (SymbolTbl.root_ident tbl)); *)
  Rewriter.eval (all_rewrites m) tbl
