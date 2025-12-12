open Smt_solver
open Ast
open Base

(* open Ast *)
(* open Frontend *)
open SmtLibAST
open Util

let define_type (fully_qual_name : qual_ident) (typ : Ast.Module.type_def) :
    unit t =
  let open State.Syntax in
  let* cmd =
    match typ.type_def_expr with
    | None -> State.return @@ Some (SmtLibAST.mk_declare_sort fully_qual_name 0)
    | Some typ_expr -> (
        match typ_expr with
        | App (Data (name, variant_decls), _, _) ->
            State.return None
        | _ ->
            State.return
            @@ Some (SmtLibAST.mk_define_sort fully_qual_name [] typ_expr))
  in

  match cmd with
  | None -> State.return ()
  | Some cmd -> write cmd

let define_datatypes (fully_qual_names_and_typs : (qual_ident * Ast.Module.type_def) list) : unit t =
let open State.Syntax in
  let* adt_defs = State.List.map fully_qual_names_and_typs ~f:(fun (fully_qual_name, typ) -> 
    match typ.type_def_expr with
    | None -> State.return None
    | Some typ_expr -> begin
      match typ_expr with
      | App (Data (name, variant_decls), _, _) ->
          let+ variant_list =
            State.List.map variant_decls ~f:(fun v ->
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

                State.return (constr_qual_ident, destr_list))
          in

          let adt_def = (fully_qual_name, [], variant_list) in
          Some adt_def
      | _ -> State.return None
      end
  ) in

  let adt_defs = List.filter_opt adt_defs in

  let cmd = match adt_defs with
  | [] -> assert false
  | [adt_def] -> SmtLibAST.mk_declare_datatype adt_def
  | _ -> SmtLibAST.mk_declare_datatypes adt_defs in

  let* _ = write cmd in

  State.return ()



let rec check_stmt curr_callable (stmt : Stmt.t) : unit t =
  let open State.Syntax in
  match stmt.stmt_desc with
  | Block block_desc ->
      let* _ = State.List.iter block_desc.block_body ~f:(check_stmt curr_callable) in
      State.return ()
  | Cond ({ cond_test = Some test; _ } as cond_desc) ->
      let* _ = push_path_condn test in
      let* _ = check_stmt curr_callable cond_desc.cond_then in
      let* _ = pop_path_condn in

      let* _ = push_path_condn (Expr.mk_not test) in
      let* _ = check_stmt curr_callable cond_desc.cond_else in
      let* _ = pop_path_condn in

      State.return ()
  | Cond cond_desc ->
      Error.unsupported_error (Stmt.to_loc stmt)
        "Non-deterministic choice is currently not supported."
  | Basic basic_stmt -> (
      match basic_stmt with
      | Spec (spec_kind, spec) -> (
          let* _ =
            match spec.spec_comment with
            | None -> State.return ()
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
                  Error.fail_with (Stmt.spec_error_msg spec curr_callable (Stmt.to_loc stmt))
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
  let open State.Syntax in
  let call_decl = callable.call_decl in

  match callable.call_def with
  | FuncDef { func_body = None } -> (
      if
        Poly.(
          call_decl.call_decl_kind = Pred
          || call_decl.call_decl_kind = Invariant)
      then State.return ()
      else
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
                  ~data:(
                    if Int.(List.length call_decl.call_decl_returns = 1) then fn_call_expr else
                      Expr.mk_tuple_lookup fn_call_expr i
                )
              )
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

        match call_decl.call_decl_postcond with
        | [] -> State.return ()
        | _ -> assume_expr post_cond_expr)
  | FuncDef { func_body = Some expr } -> (
      match call_decl.call_decl_kind with
      | Pred | Invariant -> State.return ()
      | _ ->
        let spec_expr =
          let extra_validInhale_trigs = 
            let qual_ident_suffix = QualIdent.unqualify fully_qual_name in
            let heap_utils_valid_ident = ProgUtils.heap_utils_valid_ident Loc.dummy in
            let heap_utils_valid_inhale_ident = ProgUtils.heap_utils_valid_inhale_ident Loc.dummy in
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
                  ~data:(
                    if Int.(List.length call_decl.call_decl_returns = 1) then fn_call_expr else
                      Expr.mk_tuple_lookup fn_call_expr i
                  )
              )
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

        let* _ = assume_expr spec_expr in

        let* b =
          if callable.call_decl.call_decl_is_free
          then State.return true
          else check_valid check_contract_expr
        in

        match b with
        | true -> (
            match call_decl.call_decl_postcond with
            | [] -> State.return ()
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
              State.List.iter
                (call_decl.call_decl_formals @ call_decl.call_decl_returns
               @ call_decl.call_decl_locals)
                ~f:(fun local ->
                  write
                    (mk_declare_const
                       (QualIdent.from_ident local.var_name)
                       local.var_type))
            in

            let* _ = check_stmt fully_qual_name stmt in

            let* _ = pop in

            State.return ()
        | _ ->
          Logs.debug (fun m -> m "Skipping %b" callable.call_decl.call_decl_is_free);
          State.return ()
      in

      (* State.return () *)
      match (call_decl.call_decl_kind, call_decl.call_decl_is_auto) with
      | Lemma, true ->
        let* _ =
          write_comment
            (Stdlib.Format.asprintf "Auto lemma: %a" QualIdent.pr
               fully_qual_name)
        in
        begin
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
        end
      | _ -> State.return ())

let check_members (mod_name : ident) (deps : QualIdent.t list list) tbl =
  let open Rewriter.Syntax in
  let declare_fn (fully_qual_name: qual_ident) (sym: Module.symbol) : unit t =
    match sym with
    | CallDef c -> begin
      match c.call_def with
      | FuncDef _ ->
        let call_decl = c.call_decl in
        let cmd =
          SmtLibAST.mk_declare_fun ~loc:call_decl.call_decl_loc fully_qual_name
            (List.map call_decl.call_decl_formals ~f:(fun arg -> arg.var_type))
            (Ast.Type.mk_prod call_decl.call_decl_loc
              (List.map call_decl.call_decl_returns ~f:(fun arg ->
                    arg.var_type)))
        in
        write cmd
      | ProcDef _ -> assert false
      end
    | _ -> assert false
  in

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
  let* smt_env = get_state in
  let* _ = State.List.map deps ~f:(fun dep ->
      let dep_sym = 
        List.map dep ~f:(fun qual_name ->
          let tbl1 = SymbolTbl.goto qual_name tbl in
          let _, symbol = Rewriter.eval ~update:false (Rewriter.find_and_reify qual_name) tbl1 in
          (qual_name, symbol))  
      in
      
      let dep_sym_fn = List.filter dep_sym ~f:(function
        | _, Module.CallDef { call_def = FuncDef _; _ } -> true
        | _ -> false)
      in

      let* _ = State.List.iter dep_sym_fn ~f:(fun (qual_name, sym) ->
        declare_fn qual_name sym
      )
      in

      let data_types = List.filter_map dep_sym ~f:(function
      | qual_ident, Module.TypeDef ({ type_def_expr = Some (App (Data _, _, _)); _ } as typ_def) -> Some (qual_ident, typ_def)
      | _ -> None
      ) in

      let* _ = 
        if List.is_empty data_types then
          Rewriter.return ()
        else
          let+ _ = define_datatypes data_types in
          ()
      in

      State.List.iter dep_sym ~f:(fun (qual_name, sym) -> check_member qual_name sym))
  in
  pop

let check_module (module_def : Ast.Module.t) (tbl : SymbolTbl.t)
    (smt_env : smt_env) : smt_env =
  let dependencies, auto_dependencies = Dependencies.analyze tbl module_def smt_env.auto_dependencies in

  Logs.debug (fun m ->
      m "Dependencies: %a"
        (Util.Print.pr_list_sep " ]]\n" (Util.Print.pr_list_comma QualIdent.pr))
        dependencies);

  let smt_env = { smt_env with auto_dependencies } in 
  
  let smt_env, _ =
    State.eval
      (check_members module_def.mod_decl.mod_decl_name dependencies tbl) smt_env
  in
  smt_env
