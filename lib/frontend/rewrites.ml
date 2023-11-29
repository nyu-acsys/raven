open Base
open Ast
open Util

let rec collect_vars (expr: expr) : expr list =
  match expr with
  | App (constr, expr_list, _) ->
    let init_list =
      match constr with
      | Var _ -> [expr] 
      | _ -> []
    in

    List.fold (List.map expr_list ~f:collect_vars) ~init:init_list ~f:(List.append)

  | Binder (_, v_l, expr, _) ->
    let var_expr_list = collect_vars expr in

    List.filter var_expr_list ~f:(fun var ->
      List.fold v_l ~init:false ~f:(fun b var_decl ->
        b || (QualIdent.equal (QualIdent.from_ident var_decl.var_name) (Expr.to_qual_ident var))
      )
    )

let rec rewrite_compr_expr (expr: expr) : expr Rewriter.t =
  let open Rewriter.Syntax in
  match expr with
  | Binder (Compr, v_l, inner_expr, _expr_attr) ->
    let* _ = Rewriter.add_locals v_l
    and* inner_expr = rewrite_compr_expr inner_expr in
        
    let compr_fn_ident = Ident.fresh (Expr.to_loc expr) "compr" in

    let free_var_exprs = collect_vars inner_expr in
    
    let formal_var_decls = List.map free_var_exprs ~f:(fun var ->
        { Type.var_name = Ident.fresh (Expr.to_loc inner_expr) "tmp";
          var_loc = Expr.to_loc inner_expr;
          var_type = Expr.to_type var;
          var_const = false;
          var_ghost = false;
          var_implicit = false;
        }
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
      Expr.mk_app ~typ:(ret_typ) ~loc:(Expr.to_loc expr) (Expr.Var compr_fn_qual_ident) free_var_exprs
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
        let curr_loop_args = Stmt.stmt_local_vars_accessed loop.loop_postbody in
        let+ curr_loop_arg_var_decls = Rewriter.List.map curr_loop_args ~f:(fun var -> 
          let+ symbol = Rewriter.find_and_reify stmt.stmt_loc (QualIdent.from_ident var) in
          
          (match symbol with
          | VarDef v -> v.var_decl
          | _ -> Error.error stmt.stmt_loc "Expected a variable")
        ) in
      
        (* redefined loop_args for uniqueness *)
        let loop_arg_var_decls = List.map curr_loop_arg_var_decls ~f:(fun var_decl -> 
          { var_decl with var_name = Ident.fresh stmt.stmt_loc var_decl.var_name.ident_name }
        ) in

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

    let new_stmt = 
      let lhs_list = List.map curr_loop_ret_var_decls ~f:(fun var_decl -> QualIdent.from_ident var_decl.var_name) in
      let args_list = List.map curr_loop_arg_var_decls ~f:(fun var_decl -> Expr.from_var_decl var_decl) in

      Stmt.mk_call ~loc:(Stmt.loc stmt) ~lhs:lhs_list (QualIdent.from_ident loop_proc_name) args_list in

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

    let postconds_assume_stmts = List.map postconds_spec ~f:(fun spec -> Stmt.mk_assert_spec ~loc:stmt.stmt_loc spec) in

    let assume_false = Stmt.mk_assume_expr ~loc:stmt.stmt_loc (Expr.mk_bool ~loc:stmt.stmt_loc false) in

    let new_stmt = Stmt.mk_block_stmt ~loc:stmt.stmt_loc (postconds_assume_stmts @ [assume_false]) in

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
            List.exists (Expr.expr_local_accesses spec_form) ~f:(
              fun iden -> Ident.equal var_decl.var_name iden
            )
        ) in

        let spec_form = Expr.mk_binder ~loc:stmt.stmt_loc ~typ:Type.bool Exists used_implicit_vars spec_form in

        { spec with spec_form }
      in

      let exhale_stmts = List.map call_decl.call_decl_precond ~f:(fun spec -> Stmt.mk_exhale_spec ~loc:stmt.stmt_loc (build_correct_spec spec)) in

      (* TODO: Make sure implicit vars that appear in postconditions are being treated properly *)
      let inhale_stmts = List.map call_decl.call_decl_postcond ~f:(fun spec -> Stmt.mk_inhale_spec ~loc:stmt.stmt_loc (build_correct_spec spec)) in

      let new_stmt = Stmt.mk_block_stmt ~loc:stmt.stmt_loc (exhale_stmts @ inhale_stmts) in
      
      Rewriter.return new_stmt

    | FuncDef _ -> 
      let exhale_stmts = List.map call_decl.call_decl_precond ~f:(fun spec -> Stmt.mk_exhale_spec ~loc:stmt.stmt_loc spec) in

      let new_stmt = Stmt.mk_block_stmt ~loc:stmt.stmt_loc (exhale_stmts @ [stmt]) in
      
      Rewriter.return new_stmt
    )


  | _ -> Rewriter.Stmt.descend stmt ~f:rewrite_call_stmts


let rec all_rewrites (m: Module.t) : Module.t Rewriter.t =
  let open Rewriter.Syntax in
  let* m = Rewriter.Module.rewrite_expressions ~f:rewrite_compr_expr m in
  (* let* m = Rewriter.Module.rewrite_stmts ~f:rewrite_loops m in *)
  (* let* m = Rewriter.Module.rewrite_stmts ~f:rewrite_ret_stmts m in
  let* m = Rewriter.Module.rewrite_stmts ~f:rewrite_fold_unfold_stmts m in
  let* m = Rewriter.Module.rewrite_stmts ~f:rewrite_call_stmts m in *)

  Rewriter.return m



let process_module ?(tbl = SymbolTbl.create ()) (m: Module.t) = 
  assert (SymbolTbl.curr_is_root tbl);
  assert Ident.(m.mod_decl.mod_decl_name = QualIdent.to_ident (SymbolTbl.root_ident tbl));
  Rewriter.eval (all_rewrites m) tbl