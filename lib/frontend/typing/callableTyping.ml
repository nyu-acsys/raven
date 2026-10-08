(** Type checking of callables, their contracts and opens clauses. *)

open Base
open Ast
open Util
open TypingMonad
open TypingErrors
open ProgUtils

(* Checks an `opens` clause. Each entry names an invariant, with either no
     arguments (any instance) or one per parameter of the invariant, implicit
     ones included, of which a trailing run may be `_`; the `_`s are dropped,
     leaving the prefix a mask entry records. Arguments may only mention the callable's formals --
     except, for an atomic callable, its implicit ones, which [openAU] gives a
     fresh value (see [Masks.compute_proc_lemma_mask]). *)
let process_opens_clause (call_decl : Callable.call_decl) (formals : Type.var_decl list)
    (precond : Stmt.spec list) (postcond : Stmt.spec list)
    (disam_tbl : DisambiguationTbl.t) (mask : Callable.mask) : Callable.mask t =
  let open Rewriter.Syntax in
  let () =
    match call_decl.call_decl_kind with
    | Proc | Lemma -> ()
    | Func | Pred | Invariant ->
        Error.type_error call_decl.call_decl_loc
          (Printf.sprintf
             !"%{Ident} may not have an opens clause; only procedures and lemmas can"
             call_decl.call_decl_name)
  in
  let is_atomic =
    List.exists (precond @ postcond) ~f:(fun spec -> spec.Stmt.spec_atomic)
  in
  let allowed =
    List.filter_map formals ~f:(fun vd ->
        if is_atomic && vd.Type.var_implicit then None else Some vd.var_name)
    |> Set.of_list (module Ident)
  in
  let is_wildcard e =
    Expr.is_ident e && String.equal (Ident.name (Expr.to_ident e)) "_"
  in
  Rewriter.List.map mask ~f:(fun (qi, args) ->
      let loc = QualIdent.to_loc qi in
      let* qi, symbol =
        let* id = StmtTyping.disambiguate_ident qi disam_tbl in
        Rewriter.resolve_and_find id
      in
      let* symbol = Rewriter.Symbol.reify symbol in
      let inv_decl =
        match symbol with
        | CallDef { call_decl = { call_decl_kind = Invariant; _ } as inv_decl; _ } ->
            inv_decl
        | _ ->
            Error.type_error loc
              (Printf.sprintf
                 !"Expected an invariant in this opens clause, but found %s %{QualIdent}"
                 (Symbol.kind symbol) qi)
      in
      let inv_params = inv_decl.call_decl_formals @ inv_decl.call_decl_returns in
      let () =
        if (not (List.is_empty args)) && List.length args <> List.length inv_params then
          Error.type_error loc
            (Printf.sprintf
               !"Invariant %{Ident} takes %d argument(s), but %d are given here; write \
                 `_` for an argument left unspecified"
               inv_decl.call_decl_name (List.length inv_params) (List.length args))
      in
      let prefix = List.take_while args ~f:(fun e -> not (is_wildcard e)) in
      let+ prefix =
        Rewriter.List.map2_exn prefix
          (List.take inv_params (List.length prefix))
          ~f:(fun arg param ->
            let+ arg =
              StmtTyping.disambiguate_process_expr arg
                (Type.set_ghost true param.Type.var_type)
                disam_tbl
            in
            let () =
              match Set.choose (Set.diff (Expr.local_vars arg) allowed) with
              | None -> ()
              | Some ident ->
                  Error.type_error (Expr.to_loc arg)
                    (Printf.sprintf
                       !"%{String} cannot be used in an opens clause; arguments may only \
                         mention the callable's formals%s"
                       (Ident.name ident)
                       (if is_atomic then ", other than implicit ones" else ""))
            in
            arg)
      in
      (qi, prefix))

let process_callable (callable : Callable.t) : Module.symbol t =
  let open Rewriter.Syntax in
  let* () =
    Rewriter.Logs.debug (fun printers m ->
        m "Typing.process_callable: Start Processing callable: %a" printers.pr_callable
          callable)
  in
  let* _ = Rewriter.enter_callable callable in
  let disam_tbl = DisambiguationTbl.push [] in
  let call_decl = Callable.to_decl callable in
  let process_decls var_decls disam_tbl =
    Rewriter.List.fold_map var_decls ~init:disam_tbl ~f:(fun disam_tbl var_decl ->
        let+ var_decl = TypeExpr.process_var_decl var_decl in
        let var_decl', disam_tbl = DisambiguationTbl.add_var_decl var_decl disam_tbl in
        (disam_tbl, var_decl'))
  in
  (* A location parameter's field must name a field. It is otherwise
       presentational -- the parameter itself is an ordinary Ref -- so this is
       the only thing to check about it. *)
  let* call_decl_loc_params =
    Rewriter.List.map call_decl.call_decl_loc_params ~f:(fun field ->
        let* field, symbol = Rewriter.resolve_and_find field in
        let+ symbol = Rewriter.Symbol.reify symbol in
        match symbol with
        | Module.FieldDef _ -> field
        | _ ->
            Error.type_error (QualIdent.to_loc field)
              (Printf.sprintf
                 !"Expected a field in the location parameter of %{Ident}, but found %s \
                   %{QualIdent}"
                 call_decl.call_decl_name (Symbol.kind symbol) field))
  in
  (* TODO: Add a check to make sure that all the implicit ghost variables are declared at the end. *)
  let* disam_tbl, call_decl_formals =
    process_decls call_decl.call_decl_formals disam_tbl
  in
  let* disam_tbl, call_decl_returns =
    process_decls call_decl.call_decl_returns disam_tbl
  in
  let* disam_tbl, call_decl_locals = process_decls call_decl.call_decl_locals disam_tbl in

  let* ext_hooks = Rewriter.current_ext_hooks in

  Logs.debug (fun m -> m "adding formals");
  let* _ = Rewriter.add_locals call_decl_formals in

  Logs.debug (fun m -> m "adding returns");
  let* _ = Rewriter.add_locals call_decl_returns in

  Logs.debug (fun m -> m "adding locals");
  let* _ = Rewriter.add_locals call_decl_locals in

  Logs.debug (fun m -> m "done adding locals");

  let* call_decl_precond =
    Rewriter.List.map call_decl.call_decl_precond
      ~f:(StmtTyping.process_stmt_spec disam_tbl)
  and* call_decl_postcond =
    Rewriter.List.map call_decl.call_decl_postcond
      ~f:(StmtTyping.process_stmt_spec disam_tbl)
  in

  let () =
    (* Triggers on a postcondition are for the parameters of an auto lemma, each of
         which every trigger must mention. *)
    let is_auto_lemma =
      Poly.(call_decl.call_decl_kind = Lemma) && call_decl.call_decl_is_auto
    in
    List.iter call_decl_postcond ~f:(fun spec ->
        List.iter spec.spec_trigs ~f:(fun trg ->
            let loc = Expr.to_loc (List.hd_exn trg) in
            if not is_auto_lemma then
              Error.type_error loc
                "Only the postcondition of an auto lemma can have triggers";
            let mentioned =
              List.fold trg
                ~init:(Set.empty (module QualIdent))
                ~f:(fun acc e -> Expr.symbols ~acc e)
            in
            List.iter call_decl_formals ~f:(fun formal ->
                if not (Set.mem mentioned (QualIdent.from_ident formal.var_name)) then
                  Error.type_error loc
                    (Printf.sprintf "This trigger does not mention the parameter %s"
                       (Ident.name formal.var_name)))))
  in

  let () =
    (* Return variables are only meaningful once the callable has returned, so they
         must not occur in a `requires` clause -- only in `ensures` clauses. *)
    let return_qual_idents =
      List.map call_decl_returns ~f:(fun var_decl ->
          QualIdent.from_ident var_decl.var_name)
      |> Set.of_list (module QualIdent)
    in
    List.iter call_decl_precond ~f:(fun spec ->
        match Set.choose (Set.inter (Expr.symbols spec.spec_form) return_qual_idents) with
        | Some qual_ident ->
            (* Post-disambiguation, so print the plain source name rather than
                 [QualIdent.pr]/[Ident.pr]'s disambiguated `name^N` form -- same as the
                 sibling check on the callable's body below. *)
            Error.type_error (QualIdent.to_loc qual_ident)
              (Printf.sprintf
                 !"Return variable %{String} cannot be used in a requires clause; it is \
                   only in scope in ensures clauses"
                 (Ident.name (QualIdent.to_ident qual_ident)))
        | None -> ())
  in

  let () =
    (* Func/pred/invariant contracts are meant to be total -- the verifier never
         checks expressions for well-definedness, so a `requires` clause on one of
         these would be silently unenforced at any call site nested inside another
         expression. A domain restriction belongs in a guarded `ensures` instead. *)
    match (call_decl.call_decl_kind, call_decl_precond) with
    | (Func | Pred | Invariant), _ :: _ ->
        Error.type_error call_decl.call_decl_loc
          (Printf.sprintf
             !"%{Ident} may not have a requires clause; func/pred/invariant contracts \
               must be total"
             call_decl.call_decl_name)
    | _ -> ()
  in

  let call_decl_for_ext =
    { call_decl with call_decl_formals; call_decl_returns; call_decl_locals }
  in
  let* call_decl_contract_ext =
    Rewriter.List.map call_decl.call_decl_contract_ext ~f:(fun contract_ext ->
        lift
          (ext_hooks.type_check_contract_ext call_decl_for_ext contract_ext
             call_decl.call_decl_loc disam_tbl
             {
               ExtApi.get_assign_lhs =
                 (fun ~is_init:_ ?is_ghost_cmd:_ qi _state ->
                   Error.internal_error (QualIdent.to_loc qi)
                     "assignments are not permitted in a contract clause");
               expand_type_expr = (fun tp -> run_typing (TypeExpr.expand_type_expr tp));
               disambiguate_process_expr =
                 (fun e exp d ->
                   run_typing (StmtTyping.disambiguate_process_expr e exp d));
               type_mismatch_error;
               disam_tbl_add_var_decl = DisambiguationTbl.add_var_decl;
               process_symbol = !Rewriter.process_symbol_ref;
               process_stmt =
                 (fun _call_decl stmt _disam_tbl ->
                   Error.internal_error (Stmt.to_loc stmt)
                     "statements are not permitted in a contract clause");
             }))
  in

  let* call_decl_opens =
    Rewriter.Option.map call_decl.call_decl_opens
      ~f:
        (process_opens_clause call_decl call_decl_formals call_decl_precond
           call_decl_postcond disam_tbl)
  in

  Logs.debug (fun m -> m "done processing pre/post cond");
  let call_decl =
    {
      call_decl with
      call_decl_formals;
      call_decl_returns;
      call_decl_locals;
      call_decl_precond;
      call_decl_postcond;
      call_decl_contract_ext;
      call_decl_opens;
      call_decl_loc_params;
    }
  in
  let* callable =
    match callable.call_def with
    | FuncDef func_def ->
        (* FuncDefs should not have any new call_decl_locals in body because they are expressions. That is, all call_decl_locals are the arguments it takes. These are being disambiguated in the above.*)
        let+ func_body =
          Rewriter.Option.map func_def.func_body ~f:(fun expr ->
              let expected_return_type = Callable.return_type call_decl in
              let* expr =
                StmtTyping.disambiguate_process_expr expr expected_return_type disam_tbl
              in
              let () =
                (* A func's body is the single expression that defines its return
                     value, so referencing the return variable inside it is circular
                     (and, since nothing detects it as a recursive call, an
                     undetected non-terminating definition) -- unlike `ensures`,
                     where the return variable denotes the already-computed result.
                     Pred/Invariant don't have this problem: the parameters after
                     `;` in their signature aren't a computed return value at all,
                     just ordinary parameters that are meant to be used in the body
                     (e.g. `pred counter(x: Ref; v: Int) { own(x, v) }`) -- see the
                     `Pred | Invariant -> ...` case in [Checker.check_callable],
                     which never builds a defining axiom for them in the first
                     place. *)
                match call_decl.call_decl_kind with
                | Pred | Invariant | Proc | Lemma -> ()
                | Func -> (
                    let return_qual_idents =
                      List.map call_decl_returns ~f:(fun var_decl ->
                          QualIdent.from_ident var_decl.var_name)
                      |> Set.of_list (module QualIdent)
                    in
                    match
                      Set.choose (Set.inter (Expr.symbols expr) return_qual_idents)
                    with
                    | Some qual_ident ->
                        (* Post-disambiguation, so print the plain source name
                           rather than [QualIdent.pr]/[Ident.pr]'s disambiguated
                           `name^N` form. *)
                        Error.type_error (QualIdent.to_loc qual_ident)
                          (Printf.sprintf
                             !"Return variable %{String} cannot be used in the body of \
                               %{String}; it is only in scope in ensures clauses"
                             (Ident.name (QualIdent.to_ident qual_ident))
                             (Ident.name call_decl.call_decl_name))
                    | None -> ())
              in
              Rewriter.return expr)
        in

        let func_def = Callable.{ call_decl; call_def = FuncDef { func_body } } in

        func_def
    | ProcDef proc_def ->
        let+ proc_body =
          Rewriter.Option.map proc_def.proc_body ~f:(fun stmt ->
              (* Logs.debug (fun m -> m "Typing.process_callable: Processing stmt: %a" Stmt.pr stmt); *)
              Logs.debug (fun m ->
                  m "Typing.process_callable: Callable: %a" Ident.pr
                    callable.call_decl.call_decl_name);

              Logs.debug (fun m ->
                  m "Typing.process_callable: DisamTbl: %a"
                    (Fmt.Dump.list (Fmt.Dump.list (Fmt.Dump.pair Ident.pr Ident.pr)))
                    (List.map disam_tbl ~f:Map.to_alist));

              let+ stmt, _disam_tbl =
                StmtTyping.process_stmt ~new_scope:false call_decl stmt disam_tbl
              in
              stmt)
        in

        let proc_def = Callable.{ call_decl; call_def = ProcDef { proc_body } } in
        proc_def
  in
  let+ callable = Rewriter.exit_callable callable in
  Module.CallDef callable
