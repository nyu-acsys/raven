open Smt_solver
open Ast
open Base

(* open Ast *)
(* open Frontend *)
open SmtLibAST
open Util

let define_type (fully_qual_name : qual_ident) (typ : Ast.Module.type_def) :
    unit t =
  let open Rewriter.Syntax in
  let* cmd =
    match typ.type_def_expr with
    | None -> Rewriter.return @@ SmtLibAST.mk_declare_sort fully_qual_name 0
    | Some typ_expr -> (
        match typ_expr with
        | App (Data (name, variant_decls), _, _) ->
            let* variant_list =
              Rewriter.List.map variant_decls ~f:(fun v ->
                  let destr_list =
                    List.map v.variant_args ~f:(fun v_d ->
                        let destr_qual_ident =
                          QualIdent.append
                            (QualIdent.pop fully_qual_name)
                            v_d.var_name
                        in
                        (destr_qual_ident, v_d.var_type))
                  in

                  let constr_qual_ident =
                    QualIdent.append
                      (QualIdent.pop fully_qual_name)
                      v.variant_name
                  in

                  let* constr_fully_qual_name =
                    Rewriter.resolve typ.type_def_loc constr_qual_ident
                  in

                  assert (Poly.(constr_fully_qual_name = constr_qual_ident));

                  Rewriter.return (constr_fully_qual_name, destr_list))
            in

            let adt_def = (fully_qual_name, [], variant_list) in
            Rewriter.return (SmtLibAST.mk_declare_datatype adt_def)
        | _ ->
            Rewriter.return
            @@ SmtLibAST.mk_define_sort fully_qual_name [] typ_expr)
  in

  let* _ = write cmd in

  Rewriter.return ()

let rec check_stmt (stmt : Stmt.t) : unit t =
  let open Rewriter.Syntax in
  match stmt.stmt_desc with
  | Block block_desc ->
      let* _ = Rewriter.List.iter block_desc.block_body ~f:check_stmt in
      Rewriter.return ()
  | Cond ({ cond_test = Some test; _ } as cond_desc) ->
      let* _ = push_path_condn test in
      let* _ = check_stmt cond_desc.cond_then in
      let* _ = pop_path_condn in

      let* _ = push_path_condn (Expr.mk_not test) in
      let* _ = check_stmt cond_desc.cond_else in
      let* _ = pop_path_condn in

      Rewriter.return ()
  | Cond cond_desc ->
      Error.unsupported_error (Stmt.to_loc stmt)
        "Non-deterministic choice is currently not supported."
  | Basic basic_stmt -> (
      match basic_stmt with
      | Spec (spec_kind, spec) -> (
          let* _ =
            match spec.spec_comment with
            | None -> Rewriter.return ()
            | Some c -> write_comment c
          in

          match spec_kind with
          | Assume -> assume_expr spec.spec_form
          | Assert -> (
              let* b = check_valid spec.spec_form in
              match b with
              | true -> assume_expr spec.spec_form
              (* Rewriter.return () *)
              | false ->
                  let* curr_callable = Rewriter.current_scope_id in
                  Error.fail_with (Stmt.spec_error_msg spec curr_callable)
              (* match (Stmt.spec_error_msg spec curr_callable) with
                 | None -> Error.verification_error stmt.stmt_loc "Assertion is not valid"
                 | Some e ->
                   Error.verification_error stmt.stmt_loc (Stmt.spec_error_msg e curr_callable) *)
              )
          | _ -> Error.verification_error stmt.stmt_loc "Unexpected spec kind")
      | _ ->
          Error.verification_error stmt.stmt_loc
            ("Unexpected basic stmt: " ^ Stmt.to_string stmt))
  | _ -> Error.verification_error stmt.stmt_loc "Unexpected stmt"

let check_callable (fully_qual_name : qual_ident) (callable : Ast.Callable.t) :
    unit t =
  let open Rewriter.Syntax in
  let call_decl = callable.call_decl in

  match callable.call_def with
  | FuncDef { func_body = None } -> (
      if
        Poly.(
          call_decl.call_decl_kind = Pred
          || call_decl.call_decl_kind = Invariant)
      then Rewriter.return ()
      else
        let cmd =
          SmtLibAST.mk_declare_fun ~loc:call_decl.call_decl_loc fully_qual_name
            (List.map call_decl.call_decl_formals ~f:(fun arg -> arg.var_type))
            (Ast.Type.mk_prod call_decl.call_decl_loc
               (List.map call_decl.call_decl_returns ~f:(fun arg ->
                    arg.var_type)))
        in

        let ret_tuple =
          Expr.mk_tuple
            (List.map call_decl.call_decl_returns ~f:(fun arg ->
                 Expr.from_var_decl arg))
        in

        let alpha_renaming_map =
          let fn_call_expr =
            Expr.mk_app ~typ:(Expr.to_type ret_tuple) (Var fully_qual_name)
              (List.map call_decl.call_decl_formals ~f:(fun arg ->
                   Expr.from_var_decl arg))
          in

          if List.length call_decl.call_decl_returns = 1 then
            Map.singleton
              (module QualIdent)
              (QualIdent.from_ident
                 (List.hd_exn call_decl.call_decl_returns).var_name)
              fn_call_expr
          else
            List.foldi call_decl.call_decl_returns
              ~init:(Map.empty (module QualIdent))
              ~f:(fun i acc arg ->
                Map.set acc
                  ~key:(QualIdent.from_ident arg.var_name)
                  ~data:(Expr.mk_tuple_lookup fn_call_expr i))
        in

        let post_cond_expr =
          Expr.mk_binder Forall call_decl.call_decl_formals
            ~trigs:
              [
                [
                  Expr.mk_app ~typ:Ast.Type.bot (Var fully_qual_name)
                    (List.map call_decl.call_decl_formals ~f:(fun arg ->
                         Expr.from_var_decl arg));
                ];
              ]
            (Expr.mk_impl
               (Expr.mk_and
                  (List.map call_decl.call_decl_precond ~f:(fun pre ->
                       Expr.alpha_renaming pre.spec_form alpha_renaming_map)))
               (Expr.mk_and
                  (List.map call_decl.call_decl_postcond ~f:(fun post ->
                       Expr.alpha_renaming post.spec_form alpha_renaming_map))))
        in

        let* _ = write cmd in
        match call_decl.call_decl_postcond with
        | [] -> Rewriter.return ()
        | _ -> assume_expr post_cond_expr)
  | FuncDef { func_body = Some expr } -> (
      if
        Poly.(
          call_decl.call_decl_kind = Pred
          || call_decl.call_decl_kind = Invariant)
      then Rewriter.return ()
      else
        (* let cmd =
           SmtLibAST.mk_define_fun ~loc:call_decl.call_decl_loc fully_qual_name
           (List.map call_decl.call_decl_formals ~f:(fun arg -> (QualIdent.from_ident arg.var_name, arg.var_type)))
           (Type.mk_prod call_decl.call_decl_loc (List.map call_decl.call_decl_returns ~f:(fun arg -> arg.var_type)))
           expr in *)
        let cmd =
          SmtLibAST.mk_declare_fun ~loc:call_decl.call_decl_loc fully_qual_name
            (List.map call_decl.call_decl_formals ~f:(fun arg -> arg.var_type))
            (Ast.Type.mk_prod call_decl.call_decl_loc
               (List.map call_decl.call_decl_returns ~f:(fun arg ->
                    arg.var_type)))
        in
        let spec_expr =
          let extra_validInhale_trigs = 
            let qual_ident_suffix = QualIdent.unqualify fully_qual_name in
            let heap_utils_valid_ident = Rewriter.ProgUtils.heap_utils_valid_ident Loc.dummy in
            let heap_utils_valid_inhale_ident = Rewriter.ProgUtils.heap_utils_valid_inhale_ident Loc.dummy in
            let fully_qual_name_path = QualIdent.from_list (QualIdent.path fully_qual_name) in

            if Ident.(qual_ident_suffix = heap_utils_valid_inhale_ident) then begin
              Logs.debug (fun m -> m 
                "Checker.check_callable: qual_ident_suffix matched with heap_utils_valid_inhale_ident: %a"
                  Ident.pr qual_ident_suffix
              );
              let valid_ident_fully_qual_name =
                QualIdent.append fully_qual_name_path heap_utils_valid_ident
              in [ [
                Expr.mk_app ~typ:Ast.Type.bot (Var valid_ident_fully_qual_name)
                    (List.map call_decl.call_decl_formals ~f:(fun arg ->
                         Expr.from_var_decl arg)
                    );
              ] ]
            end else (
              (* if Ident.(qual_ident_suffix = heap_utils_valid_ident) then begin
                let valid_inhale_ident_fully_qual_name =
                  QualIdent.append fully_qual_name_path heap_utils_valid_inhale_ident
                in [ [
                  Expr.mk_app ~typ:Ast.Type.bot (Var valid_inhale_ident_fully_qual_name)
                      (List.map call_decl.call_decl_formals ~f:(fun arg ->
                           Expr.from_var_decl arg)
                      );
                ] ]
              end else *)
                [ ] 
            )
              
          in

          Expr.mk_binder Forall call_decl.call_decl_formals
            ~trigs: (
              [
                [
                  Expr.mk_app ~typ:Ast.Type.bot (Var fully_qual_name)
                    (List.map call_decl.call_decl_formals ~f:(fun arg ->
                         Expr.from_var_decl arg));
                ];
              ] @ extra_validInhale_trigs
            )
            (Expr.mk_eq
               (Expr.mk_app ~typ:(Expr.to_type expr) (Var fully_qual_name)
                  (List.map call_decl.call_decl_formals ~f:(fun arg ->
                       Expr.from_var_decl arg)))
               expr)
        in

        let ret_tuple =
          Expr.mk_tuple
            (List.map call_decl.call_decl_returns ~f:(fun arg ->
                 Expr.from_var_decl arg))
        in

        let alpha_renaming_map =
          let fn_call_expr =
            Expr.mk_app ~typ:(Expr.to_type ret_tuple) (Var fully_qual_name)
              (List.map call_decl.call_decl_formals ~f:(fun arg ->
                   Expr.from_var_decl arg))
          in

          if List.length call_decl.call_decl_returns = 1 then
            Map.singleton
              (module QualIdent)
              (QualIdent.from_ident
                 (List.hd_exn call_decl.call_decl_returns).var_name)
              fn_call_expr
          else
            List.foldi call_decl.call_decl_returns
              ~init:(Map.empty (module QualIdent))
              ~f:(fun i acc arg ->
                Map.set acc
                  ~key:(QualIdent.from_ident arg.var_name)
                  ~data:(Expr.mk_tuple_lookup fn_call_expr i))
        in

        let check_contract_expr =
          Expr.mk_binder Forall
            (call_decl.call_decl_formals @ call_decl.call_decl_returns)
            (Expr.mk_impl
               (Expr.mk_and
                  (Expr.mk_eq ret_tuple
                     (Expr.mk_app ~typ:(Expr.to_type ret_tuple)
                        (Var fully_qual_name)
                        (List.map call_decl.call_decl_formals ~f:(fun arg ->
                             Expr.from_var_decl arg)))
                  :: List.map call_decl.call_decl_precond ~f:(fun pre ->
                         pre.spec_form)))
               (Expr.mk_and
                  (List.map call_decl.call_decl_postcond ~f:(fun post ->
                       post.spec_form))))
        in

        let post_cond_expr =
          Expr.mk_binder Forall call_decl.call_decl_formals
            (Expr.mk_impl
               (Expr.mk_and
                  (List.map call_decl.call_decl_precond ~f:(fun pre ->
                       Expr.alpha_renaming pre.spec_form alpha_renaming_map)))
               (Expr.mk_and
                  (List.map call_decl.call_decl_postcond ~f:(fun post ->
                       Expr.alpha_renaming post.spec_form alpha_renaming_map))))
        in

        let* _ = write cmd in
        let* _ = assume_expr spec_expr in

        let* b =
          if callable.call_decl.call_decl_is_free
          then Rewriter.return true
          else check_valid check_contract_expr
        in

        match b with
        | true -> (
            match call_decl.call_decl_postcond with
            | [] -> Rewriter.return ()
            | _ -> assume_expr post_cond_expr)
        | false ->
            Error.verification_error call_decl.call_decl_loc
              (Printf.sprintf "Contract is not valid"))
  | ProcDef proc_def -> (
      let* _ =
        match proc_def.proc_body with
        | Some stmt when not callable.call_decl.call_decl_is_free ->
            let* _ = push in
            let* _ =
              write_comment
                (Stdlib.Format.asprintf "Checking %a" QualIdent.pr
                   fully_qual_name)
            in

            let* _ =
              Rewriter.List.iter
                (call_decl.call_decl_formals @ call_decl.call_decl_returns
               @ call_decl.call_decl_locals)
                ~f:(fun local ->
                  write
                    (mk_declare_const
                       (QualIdent.from_ident local.var_name)
                       local.var_type))
            in

            let* _ = check_stmt stmt in

            let* _ = pop in

            Rewriter.return ()
        | _ ->
          Logs.debug (fun m -> m "Skipping %b" callable.call_decl.call_decl_is_free);
          Rewriter.return ()
      in

      (* Rewriter.return () *)
      match (call_decl.call_decl_kind, call_decl.call_decl_is_auto) with
      | Lemma, true ->
          let* spec_is_pure =
            Rewriter.List.fold_left ~init:true
              (call_decl.call_decl_precond @ call_decl.call_decl_postcond)
              ~f:(fun acc spec ->
                let* is_pure = Rewriter.ProgUtils.is_expr_pure spec.spec_form in
                Rewriter.return (acc && is_pure))
          in

          if
            spec_is_pure
            && List.is_empty
                 (call_decl.call_decl_formals @ call_decl.call_decl_returns)
          then
            let* _ =
              write_comment
                (Stdlib.Format.asprintf "Auto lemma: %a" QualIdent.pr
                   fully_qual_name)
            in
            match call_decl.call_decl_precond with
            | [] ->
                assume_expr
                  (Expr.mk_and
                     (List.map call_decl.call_decl_postcond ~f:(fun spec ->
                          spec.spec_form)))
            | _ ->
                assume_expr
                  (Expr.mk_impl
                     (Expr.mk_and
                        (List.map call_decl.call_decl_precond ~f:(fun spec ->
                             spec.spec_form)))
                     (Expr.mk_and
                        (List.map call_decl.call_decl_postcond ~f:(fun spec ->
                             spec.spec_form))))
          else
            Error.verification_error call_decl.call_decl_loc
              (Printf.sprintf !"Auto lemma %{Ident} must have pure preconditions and postconditions, \
               and no arguments or return values" call_decl.call_decl_name)
      | _ -> Rewriter.return ())

let check_members (mod_name : ident) (deps : QualIdent.t list list) : smt_env t
    =
  let open Rewriter.Syntax in
  let check_member qual_name symbol =
    (* Logs.info (fun m -> m "Checking: %a" QualIdent.pr qual_name); *)
    match symbol with
      | Module.CallDef callable -> check_callable qual_name callable
      | TypeDef typ -> define_type qual_name typ
      | VarDef var_def -> (
          let* _ =
            write (mk_declare_const qual_name var_def.var_decl.var_type)
          in
          match var_def.var_init with
          | None -> Rewriter.return ()
          | Some expr ->
            assume_expr
              (Expr.mk_eq
                 (Expr.mk_app ~typ:(Expr.to_type expr) (Var qual_name)
                    [])
                 expr))
      | _ ->
        Error.unsupported_error Loc.dummy
          ("Unsupported symbol: " ^ Symbol.to_string symbol)
  in
  let* _ = push in
  let* _ =
    write_comment
      (Stdlib.Format.asprintf "Checking members in %a" Ident.pr mod_name)
  in
  let* _ = Rewriter.List.iter deps ~f:(fun dep ->
      let* dep_sym = Rewriter.List.map dep ~f:(fun qual_name ->
          let+ symbol = Rewriter.find_and_reify Loc.dummy qual_name in
          (qual_name, symbol))
      in
      Logs.debug (fun m -> m "Deps: %a" (Print.pr_list_comma QualIdent.pr) (List.map ~f:(fun (a,b) -> a) dep_sym));
      Rewriter.List.iter dep_sym ~f:(fun (qual_name, sym) -> check_member qual_name sym))
  in
  let* _ = pop in

  Rewriter.current_user_state

let check_module (module_def : Ast.Module.t) (tbl : SymbolTbl.t)
    (smt_env : smt_env) : smt_env =
  let dependencies, auto_dependencies = Dependencies.analyze tbl module_def smt_env.auto_dependencies in

  Logs.debug (fun m ->
      m "Dependencies: %a"
        (Util.Print.pr_list_sep " ]]\n" (Util.Print.pr_list_comma QualIdent.pr))
        dependencies);

  let smt_env = { smt_env with auto_dependencies } in 
  
  let _tbl, smt_env =
    Rewriter.eval ~update:false
      (Rewriter.eval_with_user_state ~init:smt_env
         (check_members module_def.mod_decl.mod_decl_name dependencies))
      tbl
  in
  smt_env
