open Base
open Ast

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
        b || (QualIdent.equal (QualIdent.from_ident var_decl.var_name) (AstUtil.expr_to_qual_ident var))
      )
    )

let rec rewrite_compr_expr (expr: expr) (scope: qual_ident): Callable.t list * expr = 
  match expr with
  | App (constr, expr_list, expr_attr) ->
    let fn_list, expr_list = 
      List.fold_map expr_list ~init:[] ~f:(fun fn_list expr ->
        let fn_list', expr = rewrite_compr_expr expr scope in
        
        fn_list @ fn_list', expr
      )
    in

    fn_list, App (constr, expr_list, expr_attr)

  | Binder (b, v_l, inner_expr, expr_attr) ->
    let fn_list1, inner_expr = rewrite_compr_expr inner_expr scope in

    match b with
    | Forall | Exists -> 
      fn_list1, Binder (b, v_l, inner_expr, expr_attr)

    | Compr ->
      let compr_fn_ident = Ident.fresh "compr" in

      let free_var_exprs = collect_vars inner_expr in

      let formal_var_decls = List.map free_var_exprs ~f:(fun var ->
        { Type.var_name = Ident.fresh "tmp";
          var_loc = Expr.loc inner_expr;
          var_type = Expr.to_type var;
          var_const = false;
          var_ghost = false;
          var_implicit = false;
        }
      ) in

      let formals = List.map formal_var_decls ~f:(fun var_decl -> var_decl.var_name) in

      let ret_var_decl = 
        { Type.var_name = Ident.fresh "ret";
          var_loc = Expr.loc expr;
          var_type = Expr.to_type expr;
          var_const = false;
          var_ghost = false;
          var_implicit = false;
        } 
      in

      let returns = [ret_var_decl.var_name] in

      let locals = formal_var_decls @ [ret_var_decl] in
      let locals_map = List.fold locals ~init:(Map.empty (module Ident)) ~f:(fun m var_decl ->
        Map.set m ~key:var_decl.var_name ~data:var_decl
      ) in

      let ret_typ = (Expr.to_type expr) in

      let postcond = 
        let spec_form =
          if Type.is_set ret_typ then

            let var_decl = List.hd_exn v_l in

            Expr.mk_binder ~typ:Type.bool Forall [var_decl] (
              Expr.mk_app ~typ:Type.bool Impl [
                inner_expr;
                
                Expr.mk_app ~typ:Type.bool Elem [ 
                  AstUtil.var_decl_to_expr var_decl;
                  AstUtil.var_decl_to_expr ret_var_decl
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
                    AstUtil.var_decl_to_expr ret_var_decl; AstUtil.var_decl_to_expr var_decl; ]
                ]
              )

        in

      { Stmt.spec_form = spec_form;
        spec_atomic = false;
        spec_error = None;
      } 

      in


      let func_decl = {
        Callable.call_decl_kind = Func;
        call_decl_name = compr_fn_ident;
        call_decl_formals = formals;
        call_decl_returns = returns;
        call_decl_locals = locals_map;
        call_decl_precond = [];
        call_decl_postcond = [postcond];
        call_decl_loc = Expr.loc expr;
      } 
      
      in

      let fn_list2 = [Callable.FuncDef { func_decl; func_body = None;}] in

      let new_expr = 
        Expr.mk_app ~typ:(ret_typ) (Expr.Call ((QualIdent.append scope compr_fn_ident), Expr.loc expr)) free_var_exprs
      
      in
      
      fn_list1 @ fn_list2, new_expr


let rec rewrite_compr_stmt (scope: qual_ident) (stmt: Stmt.t) : Callable.t list * Stmt.t =
  match stmt.stmt_desc with
  | Block stmt_list ->
    let fn_list, stmt_list = List.fold_map stmt_list ~init:[] ~f:(fun fn_list stmt ->
      let fn_list', stmt = rewrite_compr_stmt scope stmt in

      fn_list @ fn_list', stmt
    ) in

    fn_list, { stmt with stmt_desc = Block stmt_list; }

  | Basic basic_stmt -> begin
    match basic_stmt with 
    | VarDef var_def ->
      let fn_list, new_expr = 
        match var_def.var_init with
        | None -> [], None
        | Some expr ->
          let fn_list, new_expr = rewrite_compr_expr expr scope in

          fn_list, Some new_expr
      in

      fn_list, { stmt with stmt_desc = Basic (VarDef { var_def with var_init = new_expr; }); }

    | Spec (sk, spec) ->
      let fn_list, new_spec_form = rewrite_compr_expr spec.spec_form scope in

      fn_list, { stmt with stmt_desc = Basic (Spec (sk, { spec with spec_form = new_spec_form; })); }

    | Assign assign ->
      let fn_list, new_expr = rewrite_compr_expr assign.assign_rhs scope in

      fn_list, { stmt with stmt_desc = Basic (Assign { assign with assign_rhs = new_expr; }); }

    | Return expr_list ->
      let fn_list, expr_list = List.fold_map expr_list ~init:[] ~f:(fun fn_list expr ->
        let fn_list', expr = rewrite_compr_expr expr scope in

        fn_list @ fn_list', expr
      ) in

      fn_list, { stmt with stmt_desc = Basic (Return expr_list); }
    
    | _ -> [], stmt
    end

  | Loop loop_desc ->
    let fn_list, new_contract = List.fold_map loop_desc.loop_contract ~init:[] ~f:(fun fn_list contract ->
      let fn_list', new_spec_form = rewrite_compr_expr contract.spec_form scope in

      fn_list @ fn_list', { contract with spec_form = new_spec_form; }
    ) in

    let fn_list', new_prebody = rewrite_compr_stmt scope loop_desc.loop_prebody in

    let fn_list'', new_test = rewrite_compr_expr loop_desc.loop_test scope in

    let fn_list''', new_postbody = rewrite_compr_stmt scope loop_desc.loop_postbody in

    fn_list @ fn_list' @ fn_list'' @ fn_list''', { stmt with stmt_desc = Loop {
      loop_contract = new_contract;
      loop_prebody = new_prebody;
      loop_test = new_test;
      loop_postbody = new_postbody;
    }; }

  | Cond cond_desc ->
    let fn_list, new_test = rewrite_compr_expr cond_desc.cond_test scope in

    let fn_list', new_then_branch = rewrite_compr_stmt scope cond_desc.cond_then in

    let fn_list'', new_else_branch = rewrite_compr_stmt scope cond_desc.cond_else in

    fn_list @ fn_list' @ fn_list'', { stmt with stmt_desc = Cond {
      cond_test = new_test;
      cond_then = new_then_branch;
      cond_else = new_else_branch;
    }; }

  | Ghost ghost_desc ->
    let fn_list, new_body = rewrite_compr_stmt scope ghost_desc.ghost_body in

    fn_list, { stmt with stmt_desc = Ghost { ghost_body = new_body; }; }  


let rewrite_compr_callable (scope: qual_ident) (callable: Callable.t) : Callable.t list * Callable.t = 
  match callable with
  | Callable.FuncDef { func_decl; func_body } ->
    let new_body, fn_list = 
      match func_body with
      | None -> None, []
      | Some body ->
        let fn_list, new_body = rewrite_compr_expr body scope in

        Some new_body, fn_list
    in

    let fn_list, new_preconds = List.fold_map func_decl.call_decl_precond ~init:fn_list ~f:(fun fn_list precond ->
      let fn_list', new_spec_form = rewrite_compr_expr precond.spec_form scope in

      fn_list @ fn_list', {precond with spec_form = new_spec_form;}
    ) in

    let fn_list, new_postconds = List.fold_map func_decl.call_decl_postcond ~init:fn_list ~f:(fun fn_list postcond ->
      let  fn_list', new_spec_form = rewrite_compr_expr postcond.spec_form scope in

      fn_list @ fn_list', {postcond with spec_form = new_spec_form;}
    ) in

    let func_decl = { func_decl with 
      call_decl_precond = new_preconds;
      call_decl_postcond = new_postconds;
    } in

    fn_list, Callable.FuncDef { func_decl; func_body = new_body; }

  | Callable.ProcDef { proc_decl; proc_body } ->
    let new_body, fn_list = 
      match proc_body with
      | None -> None, []
      | Some body ->
        let fn_list, new_body = rewrite_compr_stmt scope body in

        Some new_body, fn_list
    in

    let fn_list, new_preconds = List.fold_map proc_decl.call_decl_precond ~init:fn_list ~f:(fun fn_list precond ->
      let fn_list', new_spec_form = rewrite_compr_expr precond.spec_form scope in

      fn_list @ fn_list', {precond with spec_form = new_spec_form;}
    ) in

    let fn_list, new_postconds = List.fold_map proc_decl.call_decl_postcond ~init:fn_list ~f:(fun fn_list postcond ->
      let  fn_list', new_spec_form = rewrite_compr_expr postcond.spec_form scope in

      fn_list @ fn_list', {postcond with spec_form = new_spec_form;}
    ) in

    let proc_decl = { proc_decl with 
      call_decl_precond = new_preconds;
      call_decl_postcond = new_postconds;
    } in

    fn_list, Callable.ProcDef { proc_decl; proc_body = new_body; }

let rec rewrite_compr_modules (m: Module.t) (scope: qual_ident) =  
  let new_fns, vars = List.fold_map m.members.vars ~init:[] ~f:(fun new_fns var ->
    match var.var_init with
    | None -> new_fns, var
    | Some expr ->
    let fn_list, new_expr = rewrite_compr_expr expr scope in

    let new_var = { var with var_init = Some new_expr } in

    new_fns @ fn_list, new_var
  ) in

  let new_fns, call_defs = List.fold_map m.members.call_defs ~init:new_fns ~f:(fun new_fns call_def ->
    let fn_list, new_call_def = rewrite_compr_callable scope call_def in

    new_fns @ fn_list, new_call_def
  ) in

  let mod_defs = List.map m.members.mod_defs ~f:(fun mod_def ->
    rewrite_compr_modules mod_def (QualIdent.append scope mod_def.module_decl.mod_decl_name)
  ) in

  let call_defs = new_fns @ call_defs in

  let mod_decl = { m.module_decl with 
    mod_decl_callables = 
      List.fold call_defs ~init:(Map.empty (module Ident)) ~f:(fun m callable ->
        Map.set m ~key:(Callable.to_decl callable).call_decl_name ~data:(Callable.to_decl callable)
      );

    mod_decl_mod_defs = 
      List.fold (mod_defs: Module.t list) ~init:(Map.empty (module Ident)) ~f:(fun m mod_def ->
        Map.set m ~key:(mod_def.module_decl.mod_decl_name) ~data:(mod_def.module_decl)
        
      );
  } in

  { m with 
    module_decl = mod_decl;

    members = { m.members with 
      vars = vars;
      call_defs = call_defs;
      mod_defs = mod_defs;
    }
  }
