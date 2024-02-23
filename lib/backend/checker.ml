open Smt_solver_new
open Ast
open Base
open Frontend
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
        let destr_list = List.map v.variant_args ~f:(fun v_d -> (QualIdent.from_ident v_d.var_name, v_d.var_type)) in
        let* constr_fully_qual_name = Rewriter.resolve typ.type_def_loc (QualIdent.from_ident v.variant_name) in 

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
        write (SmtLibAST.mk_assert spec.spec_form)
      | Assert ->
        let* b = check_valid spec.spec_form in
        (match b with
        | true -> Rewriter.return ()
        | false -> Error.smt_error stmt.stmt_loc "Assertion is not valid")

      | _ -> Error.smt_error stmt.stmt_loc "Unexpected spec kind")

    | _ -> Error.smt_error stmt.stmt_loc "Unexpected basic stmt"
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

      let post_cond_cmd = SmtLibAST.mk_assert 
        (Expr.mk_binder Forall call_decl.call_decl_formals 
          (Expr.mk_impl 
            (Expr.mk_eq 
              (Expr.mk_app (Var fully_qual_name) (List.map call_decl.call_decl_formals ~f:(fun arg -> Expr.from_var_decl arg))) 

              (Expr.mk_tuple (List.map call_decl.call_decl_returns ~f:(fun arg -> Expr.from_var_decl arg)))
            ) 

          (Expr.mk_and (List.map call_decl.call_decl_postcond ~f:(fun post -> post.spec_form)))  
        )
        ) in
      
      let* _ = write cmd in
      write post_cond_cmd

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
        (Expr.mk_binder Forall call_decl.call_decl_formals 
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

      let post_cond_cmd = SmtLibAST.mk_assert 
      (Expr.mk_binder Forall call_decl.call_decl_formals 
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
      | true -> write post_cond_cmd
      | false -> Error.smt_error call_decl.call_decl_loc (Printf.sprintf "Contract is not valid"))

    

  | ProcDef {proc_body = None} -> 
    Rewriter.return ()

  
  | ProcDef {proc_body = Some stmt} -> 
    let* _ = push in

    let* _ = Rewriter.List.iter call_decl.call_decl_locals ~f:(fun local -> 
      write (mk_declare_const (QualIdent.from_ident local.var_name) local.var_type )
    ) in

    let* _ = check_stmt stmt in
    
    let* _ = pop in
      
    Rewriter.return ()


(* let start_session () =
  init (), SmtEnv.push ([], [])
  
let stop_session session =
  Smt_solver.stop_solver session *)
