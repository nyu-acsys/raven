(** Type checking of callables and their clauses. *)

open Base
open Ast
open Util
open TypingMonad
open TypingErrors
open ProgUtils

(* Checks an `opens` or `depends` clause. Invariant entries name only parameters before
   `;`; predicate dependency entries may also name implicit parameters after `;`. No
   arguments selects every instance; trailing `_` arguments are preserved. Arguments
   mention only the callable's formals, except, for an atomic callable, its implicit ones
   (see [NamespaceInference.required_specs]). *)
let check_mask_clause ~keyword (call_decl : Callable.call_decl)
    (formals : Type.var_decl list) (precond : Stmt.spec list) (postcond : Stmt.spec list)
    (disam_tbl : DisambiguationTbl.t) (entries : Callable.mask_entry list) :
    Callable.mask_entry list t =
  let open Rewriter.Syntax in
  let is_atomic =
    List.exists (precond @ postcond) ~f:(fun spec -> spec.Stmt.spec_atomic)
  in
  let allowed =
    List.filter_map formals ~f:(fun vd ->
        if is_atomic && vd.Type.var_implicit then None else Some vd.var_name)
    |> Set.of_list (module Ident)
  in
  Rewriter.List.map entries ~f:(fun (source_head, args) ->
      let qi = Callable.mask_head_name source_head in
      let loc = QualIdent.to_loc qi in
      let* qi, symbol =
        let* id = StmtTyping.disambiguate_ident qi disam_tbl in
        Rewriter.resolve_and_find id
      in
      let* symbol = Rewriter.Symbol.reify symbol in
      let resource_decl, head =
        match symbol with
        | CallDef { call_decl = { call_decl_kind = Invariant; _ } as inv_decl; _ } ->
            (inv_decl, Callable.MaskHead.Invariant qi)
        | CallDef { call_decl = { call_decl_kind = Pred; _ } as pred_decl; _ } ->
            (pred_decl, Callable.MaskHead.Dependencies qi)
        | _ -> opens_not_resource_error loc ~keyword (Symbol.kind symbol) qi
      in
      let resource_params =
        match head with
        | Callable.MaskHead.Invariant _ -> resource_decl.call_decl_formals
        | Dependencies _ ->
            resource_decl.call_decl_formals @ resource_decl.call_decl_returns
      in
      let args =
        match head with
        | Callable.MaskHead.Invariant _
          when List.length args
               = List.length resource_params + List.length resource_decl.call_decl_returns
               && List.for_all
                    (List.drop args (List.length resource_params))
                    ~f:Callable.is_opens_wildcard ->
            List.take args (List.length resource_params)
        | Invariant _ | Dependencies _ -> args
      in
      let () =
        if (not (List.is_empty args)) && List.length args <> List.length resource_params
        then
          let kind =
            match head with
            | Callable.MaskHead.Invariant _ -> "Invariant"
            | Callable.MaskHead.Dependencies _ -> "Predicate"
          in
          opens_arity_error loc resource_decl.call_decl_name ~kind
            ~expected:(List.length resource_params) ~given:(List.length args)
      in
      let prefix =
        List.take_while args ~f:(fun e -> not (Callable.is_opens_wildcard e))
      in
      let+ prefix =
        Rewriter.List.map2_exn prefix
          (List.take resource_params (List.length prefix))
          ~f:(fun arg param ->
            let+ arg =
              StmtTyping.disambiguate_and_check_expr arg
                (Type.set_ghost true param.Type.var_type)
                disam_tbl
            in
            let () =
              match Set.choose (Set.diff (Expr.local_vars arg) allowed) with
              | None -> ()
              | Some ident ->
                  opens_non_formal_error (Expr.to_loc arg) ~keyword ident ~is_atomic
            in
            arg)
      in
      (head, prefix @ List.drop args (List.length prefix)))

let check_ancestry (callable : Callable.t) (formals : Type.var_decl list)
    (disam_tbl : DisambiguationTbl.t) (clause : Callable.ancestry_clause) :
    Callable.ancestry_clause t =
  let open Rewriter.Syntax in
  let fail message = Error.type_error clause.ancestry_loc message in
  let () =
    match Callable.kind callable with
    | Invariant -> ()
    | Proc | Lemma | Func | Pred -> fail "Only invariants may declare a within clause"
  in
  let* owner = Rewriter.current_module_name in
  let* owner_symbol = Rewriter.find_absolute owner in
  (* In a concrete module, the clause declares the invariant's parent. *)
  let ancestry_kind =
    match owner_symbol with
    | Some (Module.ModDef { mod_decl; _ })
      when mod_decl.mod_decl_is_interface
           || Option.is_some mod_decl.mod_decl_sealed_target ->
        Callable.Within
    | _ -> Parent
  in
  let () =
    match ancestry_kind with
    | Parent when Callable.is_abstract callable ->
        fail
          "A within clause of an invariant in a concrete module requires a definition of \
           the invariant"
    | Parent | Within -> ()
  in
  let* child = Rewriter.current_scope_id in
  let* ancestry_target, target =
    Rewriter.in_scope_of child (Rewriter.resolve_and_find clause.ancestry_target)
  in
  let* target_decl =
    match Rewriter.Symbol.orig_symbol target with
    | Module.CallDef { call_decl = { call_decl_kind = Invariant; _ }; _ } ->
        Rewriter.Symbol.reify_callable_decl target
    | _ -> fail "A within clause must name an invariant"
  in
  let () =
    let same_module =
      QualIdent.equal
        (QualIdent.append owner (QualIdent.unqualify ancestry_target))
        ancestry_target
    in
    (* An implementation inherits a definition, whose ancestor is then its parent. *)
    if (not same_module) && not (Callable.is_abstract callable) then
      fail
        "A within clause of an invariant with a definition must name an invariant in the \
         same module"
  in
  let args_and_formals =
    match List.zip clause.ancestry_args target_decl.call_decl_formals with
    | Unequal_lengths ->
        fail
          (Printf.sprintf "A within clause requires %d argument(s), but %d are given"
             (List.length target_decl.call_decl_formals)
             (List.length clause.ancestry_args))
    | Ok pairs -> pairs
  in
  let+ ancestry_args =
    Rewriter.List.map args_and_formals ~f:(fun (arg, target_formal) ->
        let bad_projection () =
          Error.type_error (Expr.to_loc arg)
            "A within argument must be an explicit parameter of the child invariant"
        in
        if (not (Expr.is_ident arg)) || Callable.is_opens_wildcard arg then
          bad_projection ();
        let* arg =
          StmtTyping.disambiguate_and_check_expr arg
            (Type.set_ghost true Type.any)
            disam_tbl
        in
        if
          (not (Expr.is_ident arg))
          || not
               (List.exists formals ~f:(fun formal ->
                    (not formal.var_implicit)
                    && Ident.equal formal.var_name (Expr.to_ident arg)))
        then bad_projection ();
        let+ target_formal =
          Rewriter.in_scope_of ancestry_target (TypeExpr.check_var_decl target_formal)
        in
        let expected = target_formal.var_type in
        let actual = Expr.to_type arg in
        if not (Type.equal expected actual) then
          type_mismatch_error (Expr.to_loc arg) expected actual;
        arg)
  in
  { clause with ancestry_kind; ancestry_target; ancestry_args }

let check_alias (callable : Callable.t) target : Module.symbol t =
  let open Rewriter.Syntax in
  let decl = callable.call_decl in
  let fail message = Error.type_error decl.call_decl_loc message in
  let () =
    match decl.call_decl_kind with
    | Pred | Invariant -> ()
    | Proc | Lemma | Func -> fail "Only predicates and invariants may be resource aliases"
  in
  let () =
    Option.iter decl.call_decl_ancestry ~f:(fun clause ->
        Error.type_error clause.ancestry_loc "A resource alias cannot declare ancestry");
    if
      (not (List.is_empty decl.call_decl_precond))
      || (not (List.is_empty decl.call_decl_postcond))
      || (not (List.is_empty decl.call_decl_contract_ext))
      || Option.is_some decl.call_decl_bound
      || (not (List.is_empty decl.call_decl_locals))
      || (not (List.is_empty decl.call_decl_loc_params))
      || decl.call_decl_physical_atomic || decl.call_decl_is_inline
      || decl.call_decl_is_auto
    then fail "A resource alias cannot declare contracts, locals or callable modifiers";
    match callable.call_def with
    | FuncDef { func_body = None } -> ()
    | FuncDef { func_body = Some _ } | ProcDef _ ->
        fail "A resource alias cannot have a body"
  in
  let* target, symbol = Rewriter.resolve_and_find target in
  let* symbol = Rewriter.Symbol.reify symbol in
  let target_decl =
    match symbol with
    | Module.CallDef target_call
      when Poly.(target_call.call_decl.call_decl_kind = decl.call_decl_kind) ->
        target_call.call_decl
    | _ -> fail "A resource alias must name a resource of the same kind"
  in
  let check_parameters parameters expected =
    let* parameters = Rewriter.List.map parameters ~f:TypeExpr.check_var_decl in
    let* pairs =
      match List.zip parameters expected with
      | Ok pairs -> Rewriter.return pairs
      | Unequal_lengths ->
          fail "A resource alias must preserve the target's parameter shape"
    in
    let+ () =
      Rewriter.List.iter pairs ~f:(fun (parameter, expected) ->
          let* expected_type = TypeExpr.expand_type_expr expected.Type.var_type in
          let+ parameter_type = TypeExpr.expand_type_expr parameter.Type.var_type in
          if
            (not (Type.equal parameter_type expected_type))
            || Bool.(parameter.var_ghost <> expected.var_ghost)
            || Bool.(parameter.var_implicit <> expected.var_implicit)
            || Bool.(parameter.var_const <> expected.var_const)
          then
            fail "A resource alias must preserve the target's parameter types and modes")
    in
    parameters
  in
  let* call_decl_formals =
    check_parameters decl.call_decl_formals target_decl.call_decl_formals
  in
  let+ call_decl_returns =
    check_parameters decl.call_decl_returns target_decl.call_decl_returns
  in
  Module.CallDef
    {
      callable with
      call_decl =
        { decl with call_decl_formals; call_decl_returns; call_decl_alias = Some target };
    }

let check_definition (callable : Callable.t) : Module.symbol t =
  let open Rewriter.Syntax in
  let source = Callable.source_ident callable in
  (* The holes of a mixfix name, e.g. 3 for [_[_:=_]], which its explicit parameters fill. *)
  let holes =
    match Ident.name source with
    | "_[_.._]" | "_[_:=_]" -> Some 3
    | "_[.._]" | "_[_..]" | "_[_]" -> Some 2
    | name
      when String.mem name '|'
           && String.length name > 0
           && List.mem [ '('; '['; '{'; '<' ] name.[0] ~equal:Char.equal ->
        Some (if String.mem name '_' then 1 else 0)
    | _ -> None
  in
  (* A mixfix operator is a func; parameters beyond its holes are implicit and ghost. *)
  let () =
    Option.iter holes ~f:(fun holes ->
        let decl = callable.call_decl in
        if Poly.(decl.call_decl_kind <> Func) then
          mixfix_not_function_error (Ident.to_loc source);
        let explicit, implicit = List.split_n decl.call_decl_formals holes in
        if
          List.length explicit <> holes
          || List.exists explicit ~f:(fun p -> p.Type.var_implicit)
          || List.exists implicit ~f:(fun p -> not (p.Type.var_implicit && p.var_ghost))
        then mixfix_parameters_error (Ident.to_loc source) source holes)
  in
  let* () =
    Rewriter.Logs.debug (fun printers m ->
        m "CallableTyping.check: Start Processing callable: %a" printers.pr_callable
          callable)
  in
  let* _ = Rewriter.enter_callable callable in
  let disam_tbl = DisambiguationTbl.push [] in
  let call_decl = Callable.to_decl callable in
  let () =
    if call_decl.call_decl_physical_atomic then begin
      if Poly.(call_decl.call_decl_kind <> Proc) then
        Error.type_error call_decl.call_decl_loc
          "Only procedures may be physically atomic";
      if Callable.is_atomic call_decl then
        Error.type_error call_decl.call_decl_loc
          "An atomic proc cannot have atomic requires or atomic ensures clauses"
    end
  in
  (* The implicit parameters of a predicate follow its `;`. *)
  let () =
    if Poly.(call_decl.call_decl_kind = Pred) then
      List.iter call_decl.call_decl_formals ~f:(fun param ->
          if param.Type.var_implicit then implicit_pred_input_error param.var_loc)
  in
  (* Checks the types of [var_decls] and adds them to [disam_tbl]. *)
  let check_decls var_decls disam_tbl =
    Rewriter.List.fold_map var_decls ~init:disam_tbl ~f:(fun disam_tbl var_decl ->
        let+ var_decl = TypeExpr.check_var_decl var_decl in
        let var_decl', disam_tbl = DisambiguationTbl.add_var_decl var_decl disam_tbl in
        (disam_tbl, var_decl'))
  in
  (* A location parameter's field must name a field; the parameter itself is a [Ref]. *)
  let* call_decl_loc_params =
    Rewriter.List.map call_decl.call_decl_loc_params ~f:(fun field ->
        let* field, symbol = Rewriter.resolve_and_find field in
        let+ symbol = Rewriter.Symbol.reify symbol in
        match symbol with
        | Module.FieldDef _ -> field
        | _ ->
            loc_param_not_field_error (QualIdent.to_loc field) call_decl.call_decl_name
              (Symbol.kind symbol) field)
  in
  (* Parameters, return variables and locals. *)
  let* disam_tbl, call_decl_formals = check_decls call_decl.call_decl_formals disam_tbl in
  let* disam_tbl, call_decl_returns = check_decls call_decl.call_decl_returns disam_tbl in
  let* disam_tbl, call_decl_locals = check_decls call_decl.call_decl_locals disam_tbl in

  (* The update operator returns a value of the type of its container. *)
  let () =
    if String.equal (Ident.name source) "_[_:=_]" then
      match (call_decl_formals, call_decl_returns) with
      | container :: _, [ result ]
        when Type.equal
               (Type.set_ghost false container.var_type)
               (Type.set_ghost false result.var_type) ->
          ()
      | _ -> update_operator_type_error (Ident.to_loc source)
  in

  let* ext_hooks = Rewriter.current_ext_hooks in

  (* The contract, with the parameters, return variables and locals in scope. *)
  let* _ = Rewriter.add_locals call_decl_formals in

  let* _ = Rewriter.add_locals call_decl_returns in

  let* _ = Rewriter.add_locals call_decl_locals in

  let* call_decl_ancestry =
    Rewriter.Option.map call_decl.call_decl_ancestry
      ~f:(check_ancestry callable call_decl_formals disam_tbl)
  in

  let* call_decl_precond =
    Rewriter.List.map call_decl.call_decl_precond ~f:(StmtTyping.check_spec disam_tbl)
  and* call_decl_postcond =
    Rewriter.List.map call_decl.call_decl_postcond ~f:(StmtTyping.check_spec disam_tbl)
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
            if not is_auto_lemma then trigger_outside_auto_lemma_error loc;
            ExprTyping.check_triggers_mention ~kind:"parameter" call_decl_formals [ trg ]))
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
            (* Prints the source name, without disambiguation, like the check on the body
               below. *)
            return_var_in_requires_error (QualIdent.to_loc qual_ident)
              (Ident.name (QualIdent.to_ident qual_ident))
        | None -> ())
  in

  let () =
    (* Contracts of funcs, preds and invariants must be total: a [requires] would go
       unchecked at a call inside an expression. A domain restriction belongs in a guarded
       [ensures]. *)
    match (call_decl.call_decl_kind, call_decl_precond) with
    | (Func | Pred | Invariant), _ :: _ ->
        requires_on_pure_callable_error call_decl.call_decl_loc call_decl.call_decl_name
    | _ -> ()
  in

  (* Contract clauses added by extensions. *)
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
               disambiguate_and_check_expr =
                 (fun e exp d ->
                   run_typing (StmtTyping.disambiguate_and_check_expr e exp d));
               type_mismatch_error;
               disam_tbl_add_var_decl = DisambiguationTbl.add_var_decl;
               check_symbol = !Rewriter.check_symbol_ref;
               check_stmt =
                 (fun _call_decl stmt _disam_tbl ->
                   Error.internal_error (Stmt.to_loc stmt)
                     "statements are not permitted in a contract clause");
             }))
  in

  (* What a procedure or lemma may open, or an abstract resource may depend on. *)
  let* call_decl_bound =
    Rewriter.Option.map call_decl.call_decl_bound
      ~f:(fun (clause : Callable.bound_clause) ->
        begin match (clause.bound_kind, call_decl.call_decl_kind) with
        | Opens, (Proc | Lemma) -> ()
        | Opens, (Func | Pred | Invariant) ->
            opens_on_pure_callable_error call_decl.call_decl_loc call_decl.call_decl_name
        | Depends, (Pred | Invariant) when Callable.is_abstract callable -> ()
        | Depends, (Pred | Invariant) -> depends_on_definition_error clause.bound_loc
        | Depends, (Proc | Lemma | Func) ->
            depends_on_non_resource_error call_decl.call_decl_loc call_decl.call_decl_name
        end;
        let+ bound_entries =
          check_mask_clause
            ~keyword:(Callable.bound_keyword clause.bound_kind)
            call_decl call_decl_formals call_decl_precond call_decl_postcond disam_tbl
            clause.bound_entries
        in
        { clause with bound_entries })
  in

  let call_decl =
    {
      call_decl with
      call_decl_formals;
      call_decl_returns;
      call_decl_locals;
      call_decl_precond;
      call_decl_postcond;
      call_decl_contract_ext;
      call_decl_bound;
      call_decl_ancestry;
      call_decl_loc_params;
    }
  in
  (* The body. *)
  let* callable =
    match callable.call_def with
    | FuncDef func_def ->
        (* FuncDefs should not have any new call_decl_locals in body because they are expressions. That is, all call_decl_locals are the arguments it takes. These are being disambiguated in the above.*)
        (* A body that fails keeps the checked declaration, for the uses of the callable. *)
        let+ func_body =
          Rewriter.recover ~fallback:func_def.func_body
          @@ Rewriter.Option.map func_def.func_body ~f:(fun expr ->
              let expected_return_type = Callable.return_type call_decl in
              let* expr =
                StmtTyping.disambiguate_and_check_expr expr expected_return_type disam_tbl
              in
              let () =
                (* The body of a func defines its return value, so using the return
                   variable in it is circular, unlike in [ensures]. The parameters after
                   `;` of a pred or invariant are ordinary parameters. *)
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
                        (* Prints the source name, without disambiguation. *)
                        return_var_in_func_body_error (QualIdent.to_loc qual_ident)
                          (Ident.name (QualIdent.to_ident qual_ident))
                          (Ident.name call_decl.call_decl_name)
                    | None -> ())
              in
              Rewriter.return expr)
        in

        let func_def = Callable.{ call_decl; call_def = FuncDef { func_body } } in

        func_def
    | ProcDef proc_def ->
        let proc_body =
          if call_decl.call_decl_physical_atomic then
            Option.map proc_def.proc_body ~f:(fun stmt ->
                Stmt.mk_block_stmt ~loc:stmt.stmt_loc ~kind:Atomic [ stmt ])
          else proc_def.proc_body
        in
        let+ proc_body =
          Rewriter.recover ~fallback:proc_body
          @@ Rewriter.Option.map proc_body ~f:(fun stmt ->
              Logs.debug (fun m ->
                  m "CallableTyping.check: Callable: %a" Ident.pr
                    callable.call_decl.call_decl_name);

              Logs.debug (fun m ->
                  m "CallableTyping.check: DisamTbl: %a"
                    (Fmt.Dump.list (Fmt.Dump.list (Fmt.Dump.pair Ident.pr Ident.pr)))
                    (List.map disam_tbl ~f:Map.to_alist));

              let+ stmt, _disam_tbl =
                StmtTyping.check ~new_scope:false call_decl stmt disam_tbl
              in
              stmt)
        in

        let proc_def = Callable.{ call_decl; call_def = ProcDef { proc_body } } in
        proc_def
  in
  let+ callable = Rewriter.exit_callable callable in
  Module.CallDef callable

let check (callable : Callable.t) : Module.symbol t =
  match callable.call_decl.call_decl_alias with
  | Some target -> check_alias callable target
  | None -> check_definition callable
