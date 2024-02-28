open Smt_solver_new
open Ast
open Base
(* open Frontend *)
open SmtLibAST
open Util


let define_type (fully_qual_name: qual_ident) (typ: Ast.Module.type_def) : unit t =
  let open Rewriter.Syntax in

  let* cmd = 
  (match typ.type_def_expr with
  | None -> Rewriter.return @@ SmtLibAST.mk_declare_sort fully_qual_name 0
  | Some typ_expr -> (
    match typ_expr with
    | App (Data (name, variant_decls), _, _) ->

      let* variant_list = Rewriter.List.map variant_decls ~f:(fun v -> 
        
        let destr_list = List.map v.variant_args ~f:(fun v_d -> 
          let destr_qual_ident = QualIdent.append (QualIdent.pop fully_qual_name) v_d.var_name in
          (destr_qual_ident, v_d.var_type)) in

        let constr_qual_ident = QualIdent.append (QualIdent.pop fully_qual_name) v.variant_name in
        
        let* constr_fully_qual_name = Rewriter.resolve typ.type_def_loc constr_qual_ident in 

        assert Poly.(constr_fully_qual_name = constr_qual_ident);

        Rewriter.return (constr_fully_qual_name, destr_list)
      ) in

      let adt_def = (fully_qual_name, [], variant_list) in
      Rewriter.return (SmtLibAST.mk_declare_datatype adt_def)
    | _ -> Rewriter.return @@ SmtLibAST.mk_define_sort fully_qual_name [] typ_expr
  )

  )

  in

  let* _ = write cmd in

  Rewriter.return ()


let rec check_stmt (stmt: Stmt.t) : unit t = 
  let open Rewriter.Syntax in

  match stmt.stmt_desc with
  | Block block_desc ->
    let* _ = Rewriter.List.iter block_desc.block_body ~f:check_stmt in
    Rewriter.return ()

  | Cond cond_desc -> 
    let* _ = push_path_condn cond_desc.cond_test in
    let* _ = check_stmt cond_desc.cond_then in
    let* _ = pop_path_condn in

    let* _ = push_path_condn (Expr.mk_not cond_desc.cond_test) in
    let* _ = check_stmt cond_desc.cond_else in
    let* _ = pop_path_condn in

    Rewriter.return ()

  | Basic basic_stmt ->
    (match basic_stmt with
    | Spec (spec_kind, spec) ->
      (match spec_kind with
      | Assume -> 
        assume_expr spec.spec_form
      | Assert ->
        let* b = check_valid spec.spec_form in
        (match b with
        | true -> Rewriter.return ()
        | false -> Error.smt_error stmt.stmt_loc "Assertion is not valid")

      | _ -> Error.smt_error stmt.stmt_loc "Unexpected spec kind")

    | _ -> 
      Error.smt_error stmt.stmt_loc ("Unexpected basic stmt: " ^ (Stmt.to_string stmt))
    )

  | _ -> Error.smt_error stmt.stmt_loc "Unexpected stmt"
    
    



let check_callable (fully_qual_name: qual_ident) (callable: Ast.Callable.t) : unit t =
  let open Rewriter.Syntax in

  let call_decl = callable.call_decl in

  match callable.call_def with
  | FuncDef {func_body = None} -> 
    if Poly.(call_decl.call_decl_kind = Pred || call_decl.call_decl_kind = Invariant) then
      Rewriter.return ()
    else

      let cmd = 
        SmtLibAST.mk_declare_fun ~loc:call_decl.call_decl_loc fully_qual_name 
        (List.map call_decl.call_decl_formals ~f:(fun arg -> arg.var_type)) 
        (Type.mk_prod call_decl.call_decl_loc (List.map call_decl.call_decl_returns ~f:(fun arg -> arg.var_type))) in

      let post_cond_expr =  
        (Expr.mk_binder Forall (call_decl.call_decl_formals @ call_decl.call_decl_returns) 
          (Expr.mk_impl 
            (Expr.mk_eq 
              (Expr.mk_app (Var fully_qual_name) (List.map call_decl.call_decl_formals ~f:(fun arg -> Expr.from_var_decl arg))) 

              (Expr.mk_tuple (List.map call_decl.call_decl_returns ~f:(fun arg -> Expr.from_var_decl arg)))
            ) 

          (Expr.mk_and (List.map call_decl.call_decl_postcond ~f:(fun post -> post.spec_form)))  
        )
        ) in
      
      let* _ = write cmd in
      assume_expr post_cond_expr

  | FuncDef {func_body = Some expr} -> 
    if Poly.(call_decl.call_decl_kind = Pred || call_decl.call_decl_kind = Invariant) then
      Rewriter.return ()
    else

      let cmd =
        SmtLibAST.mk_define_fun ~loc:call_decl.call_decl_loc fully_qual_name 
        (List.map call_decl.call_decl_formals ~f:(fun arg -> (QualIdent.from_ident arg.var_name, arg.var_type))) 
        (Type.mk_prod call_decl.call_decl_loc (List.map call_decl.call_decl_returns ~f:(fun arg -> arg.var_type))) 
        expr in

      let check_contract_expr = 
        (Expr.mk_binder Forall (call_decl.call_decl_formals @ call_decl.call_decl_returns)
          (Expr.mk_impl 
            (Expr.mk_and 
              (
                (Expr.mk_eq 
                  (Expr.mk_tuple (List.map call_decl.call_decl_returns ~f:(fun arg -> Expr.from_var_decl arg)))
                  (Expr.mk_app (Var fully_qual_name) (List.map call_decl.call_decl_formals ~f:(fun arg -> Expr.from_var_decl arg))) 
                )
              :: List.map call_decl.call_decl_precond ~f:(fun pre -> pre.spec_form))
            )

            (Expr.mk_and (List.map call_decl.call_decl_postcond ~f:(fun post -> post.spec_form)))  
        )
      ) in

      let post_cond_expr = 
      (Expr.mk_binder Forall (call_decl.call_decl_formals @ call_decl.call_decl_returns) 
        (Expr.mk_impl 
          (Expr.mk_eq 
            (Expr.mk_app (Var fully_qual_name) (List.map call_decl.call_decl_formals ~f:(fun arg -> Expr.from_var_decl arg))) 

            (Expr.mk_tuple (List.map call_decl.call_decl_returns ~f:(fun arg -> Expr.from_var_decl arg)))
          ) 

        (Expr.mk_and (List.map call_decl.call_decl_postcond ~f:(fun post -> post.spec_form)))  
      )
      ) in

      let* _ = write cmd in
      let* b = check_valid check_contract_expr in

      (match b with
      | true -> assume_expr post_cond_expr
      | false -> Error.smt_error call_decl.call_decl_loc (Printf.sprintf "Contract is not valid"))

    

  | ProcDef {proc_body = None} -> 
    Rewriter.return ()

  
  | ProcDef {proc_body = Some stmt} -> 
    let* _ = push in
    let* _ = write_comment (Stdlib.Format.asprintf "Checking %a" QualIdent.pr fully_qual_name) in

    let* _ = Rewriter.List.iter (call_decl.call_decl_formals @ call_decl.call_decl_returns @ call_decl.call_decl_locals) ~f:(fun local -> 
      write (mk_declare_const (QualIdent.from_ident local.var_name) local.var_type )
    ) in

    let* _ = check_stmt stmt in
    
    let* _ = pop in
      
    Rewriter.return ()



let check_members (mod_name: ident) (deps: QualIdent.t list list): smt_env t =
  let open Rewriter.Syntax in

  let* _ = push in
  let* _ = write_comment (Stdlib.Format.asprintf "Checking members in %a" Ident.pr mod_name) in

  let* _ = Rewriter.List.iter deps ~f:(fun dep ->
    match dep with
    | [qual_name] -> 
      Logs.debug (fun m -> m "Checker.check_members: Checking: %a" QualIdent.pr qual_name);
      let* symbol = Rewriter.find_and_reify (Loc.dummy) qual_name in
      begin match symbol with
      | CallDef callable -> 
        check_callable qual_name callable
      | TypeDef typ -> 
        define_type qual_name typ
      | VarDef var_def ->
        let* _ = write (mk_declare_const qual_name var_def.var_decl.var_type) in
        (match var_def.var_init with
        | None -> Rewriter.return ()
        | Some expr -> assume_expr (Expr.mk_eq (Expr.mk_app (Var qual_name) []) expr))


      | _ -> Error.unsupported_error (Loc.dummy) ("Unsupported symbol: " ^ Symbol.to_string symbol)
      end

    | [] -> assert false  
    | _ -> Error.unsupported_error (Loc.dummy) "Recursive dependencies not supported at present"
    
  ) in

  let* _ = pop in

  Rewriter.current_user_state

let check_module (module_def: Ast.Module.t) (tbl: SymbolTbl.t) (smt_env: smt_env): smt_env =
  let dependencies = Dependencies.analyze tbl module_def in

  Logs.debug (fun m -> m "Dependencies: %a" (Util.Print.pr_list_sep " ]]\n" (Util.Print.pr_list_comma QualIdent.pr)) dependencies);

  let _tbl, smt_env = Rewriter.eval ~update:false (
    Rewriter.eval_with_user_state ~init:(smt_env) (check_members module_def.mod_decl.mod_decl_name dependencies)
  ) tbl in

  smt_env

