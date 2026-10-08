(** Disambiguation of identifiers and type checking of statements. *)

open Base
open Ast
open Util
open Error
open TypingMonad
open TypingErrors
open ProgUtils

let disambiguate_ident (qual_ident : qual_ident) (disam_tbl : DisambiguationTbl.t) :
    qual_ident t =
  let open Rewriter.Syntax in
  if QualIdent.is_local qual_ident then
    let ident = qual_ident |> QualIdent.unqualify in
    let* base =
      if Predefs.is_qual_ident_au_cmnd qual_ident then Rewriter.return ident
      else
        match DisambiguationTbl.find disam_tbl ident with
        | Some iden -> Rewriter.return iden
        | None ->
            let* is_local = Rewriter.is_local qual_ident in
            if is_local then
              (* if variable is local and it doesn't exist in DisambiguationTbl, then it is not defined in scope *)
              error (QualIdent.to_loc qual_ident)
              @@ Printf.sprintf "Identifier %s unbound in scope"
                   (Ident.to_string qual_ident.qual_base)
            else Rewriter.return qual_ident.qual_base
    in
    Rewriter.return
      (QualIdent.make [] base |> QualIdent.set_loc (QualIdent.to_loc qual_ident))
  else Rewriter.return qual_ident

let rec disambiguate_expr (expr : expr) (disam_tbl : DisambiguationTbl.t) : expr t =
  let open Rewriter.Syntax in
  match expr with
  (* In `e.f`, `f` names a field or destructor, which [ExprTyping]'s [Read] case resolves,
     so only the receiver is disambiguated; otherwise a local named like the field would
     capture it. *)
  | App (Read, [ ref_expr; (App (Var _, [], _) as field_expr) ], expr_attr) ->
      let+ ref_expr = disambiguate_expr ref_expr disam_tbl in
      Expr.App (Read, [ ref_expr; field_expr ], expr_attr)
  (* The extension handles its constructs, as they may bind variables of their own (e.g. a
     `match` arm's pattern variables). *)
  | App (ExprExt expr_ext, expr_list, expr_attr) ->
      let* ext_hooks = Rewriter.current_ext_hooks in
      let+ expr_ext, expr_list =
        lift
          (ext_hooks.disambiguate_expr_ext expr_ext expr_list expr_attr disam_tbl
             { disambiguate_expr = (fun e d -> run_typing (disambiguate_expr e d)) })
      in
      Expr.App (ExprExt expr_ext, expr_list, expr_attr)
  | App (constr, expr_list, expr_attr) ->
      let* expr_list =
        Rewriter.List.map expr_list ~f:(fun expr -> disambiguate_expr expr disam_tbl)
      in

      let* constr =
        match constr with
        | Var qual_ident ->
            let+ qual_ident = disambiguate_ident qual_ident disam_tbl in
            Expr.Var qual_ident
        | DataConstr qual_ident ->
            let+ qual_ident = disambiguate_ident qual_ident disam_tbl in
            Expr.DataConstr qual_ident
        | DataDestr qual_ident ->
            let+ qual_ident = disambiguate_ident qual_ident disam_tbl in
            Expr.DataDestr qual_ident
        | _ -> Rewriter.return constr
      in
      Rewriter.return Expr.(App (constr, expr_list, expr_attr))
  | Binder (binder, var_decl_list, trgs, expr, expr_attr) ->
      let disam_tbl = DisambiguationTbl.push disam_tbl in
      let disam_tbl, var_decl_list =
        List.fold_map var_decl_list ~init:disam_tbl ~f:(fun disam_tbl var_decl ->
            let var_decl', disam_tbl =
              DisambiguationTbl.add_var_decl var_decl disam_tbl
            in
            (disam_tbl, var_decl'))
      in
      let* () =
        Rewriter.Logs.debug (fun printers m ->
            m "StmtTyping.disambiguate_expr: expr = %a" printers.pr_expr expr)
      in
      let* disambiguated_expr = disambiguate_expr expr disam_tbl in
      let* trgs =
        Rewriter.List.map trgs ~f:(fun trg ->
            Rewriter.List.map trg ~f:(fun expr -> disambiguate_expr expr disam_tbl))
      in

      Rewriter.return
        Expr.(Binder (binder, var_decl_list, trgs, disambiguated_expr, expr_attr))

let disambiguate_and_check_expr ?(allow_proc_call = false) (expr : expr)
    (expected_typ : type_expr) (disam_tbl : DisambiguationTbl.t) : expr t =
  let open Rewriter.Syntax in
  let* expr = disambiguate_expr expr disam_tbl in
  let* printers = Rewriter.current_printers in

  let+ processed_expr = ExprTyping.check ~allow_proc_call expr expected_typ in

  Logs.debug (fun m ->
      m "StmtTyping.disambiguate_and_check_expr: processed_expr = %a" printers.pr_expr
        processed_expr);

  processed_expr

let disambiguate_and_check_field_read ref field disam_tbl =
  let open Rewriter.Syntax in
  let* resolved_opt = Rewriter.resolve_and_find_opt field in
  let* field, symbol =
    match resolved_opt with
    | Some resolved -> Rewriter.return resolved
    | None -> (
        (* An unqualified field or destructor imported from an uninstantiated functor is
           recovered as in [ExprTyping]'s [Read] case: the deferred import first, then the
           type of `ref`. *)
        let* imported = Rewriter.find_import_target field in
        let candidate = Base.Option.value imported ~default:field in
        let* peeked_ref = disambiguate_and_check_expr ref Type.any disam_tbl in
        let* resolved_qi =
          ImplicitInstantiation.try_resolve_implicit_instantiation_destr
            ~field_ident:candidate ~arg_typ:(Expr.to_type peeked_ref)
        in
        match resolved_qi with
        | Some resolved_qi -> Rewriter.resolve_and_find resolved_qi
        | None -> Rewriter.resolve_and_find field)
  in
  let* symbol = Rewriter.Symbol.reify symbol in
  match symbol with
  | FieldDef { field_type = App (Fld, [ field_type ], _); _ } ->
      let+ ref = disambiguate_and_check_expr ref Type.ref disam_tbl in
      (ref, field, field_type, symbol)
  | DestrDef { destr_arg; destr_return_type; _ } ->
      let+ arg = disambiguate_and_check_expr ref destr_arg disam_tbl in
      (arg, field, destr_return_type, symbol)
  | _ ->
      Error.type_error (QualIdent.to_loc field)
        (Printf.sprintf
           !"Expected field identifier but found %s %{QualIdent}"
           (Symbol.kind symbol) field)

let check_spec (disam_tbl : DisambiguationTbl.t) (spec : Stmt.spec) : Stmt.spec t =
  let open Rewriter.Syntax in
  let* _ = Rewriter.enter_ghost true in
  let* spec_form = disambiguate_and_check_expr spec.spec_form Type.perm disam_tbl in
  let* spec_trigs =
    Rewriter.List.map spec.spec_trigs ~f:(fun trg ->
        Rewriter.List.map trg ~f:(fun e ->
            disambiguate_and_check_expr e (Type.any |> Type.set_ghost true) disam_tbl))
  in
  let+ _ = Rewriter.exit_ghost in
  { spec with spec_form; spec_trigs }

let check_au_action (call_decl : Callable.call_decl) (assign_lhs : qual_ident list)
    (var_decls_lhs : var_decl list) qual_ident args (loc : location)
    (disam_tbl : DisambiguationTbl.t) : (Stmt.basic_stmt_desc * DisambiguationTbl.t) t =
  let open Rewriter.Syntax in
  let _ =
    List.iter2_exn assign_lhs var_decls_lhs ~f:(fun qual_ident var_decl ->
        if var_decl.var_type |> Type.is_ghost then ()
        else
          Error.type_error
            (qual_ident |> QualIdent.to_loc)
            "Ghost command cannot assign to non-ghost variable")
  in
  match args with
  | _ when QualIdent.(qual_ident = QualIdent.from_ident Predefs.fpu_ident) ->
      (* fpu *)
      let field_opt = function
        | Expr.App (Var qual_ident, [], _) ->
            let* field_qual_ident, symbol = Rewriter.resolve_and_find qual_ident in
            let+ symbol = Rewriter.Symbol.reify symbol in
            begin match symbol with
            | FieldDef field_decl when not field_decl.field_is_ghost ->
                Error.type_error (QualIdent.to_loc qual_ident)
                  "Frame-preserving updates ('fpu') can only be applied to ghost fields \
                   whose value is a resource algebra (RA) element"
            | FieldDef { field_type = App (Fld, [ given_type ], _); _ } ->
                Some (field_qual_ident, given_type)
            | _ -> None
            end
        | _ -> Rewriter.return None
      in
      let* ref_expr, field, fpu_exprs =
        let* opt_list =
          match args with
          | Expr.App (Read, [ ref_expr; field_expr ], _) :: expr2 :: expr3_opt ->
              let* field = field_opt field_expr in
              field
              |> Rewriter.Option.map ~f:(fun field ->
                  Rewriter.return (ref_expr, field, expr2 :: expr3_opt))
          | _ -> Rewriter.return None
        in
        opt_list
        |> Rewriter.Option.lazy_value ~default:(fun () ->
            match args with
            | expr1 :: expr2 :: expr3_opt ->
                let* field = field_opt expr2 in
                let* field =
                  Rewriter.Option.map field ~f:(fun field_qual_ident ->
                      Rewriter.return (expr1, field_qual_ident, expr3_opt))
                in
                Rewriter.Option.lazy_value field ~default:(fun () ->
                    Error.type_error (Expr.to_loc expr1) "Expected field location")
            | _ -> Error.type_error loc "Could not find field location in fpu")
      in
      let* ref_expr =
        disambiguate_and_check_expr ref_expr (Type.ref |> Type.set_ghost true) disam_tbl
      in
      let field_qual_ident, given_type = field in
      let+ fpu_exprs =
        Rewriter.List.map fpu_exprs ~f:(fun fpu_expr ->
            disambiguate_and_check_expr fpu_expr given_type disam_tbl)
      in

      let old_val_expr, new_val_expr =
        match fpu_exprs with
        | [ old_val_expr; new_val_expr ] -> (Some old_val_expr, new_val_expr)
        | [ new_val_expr ] -> (None, new_val_expr)
        | _ -> Error.type_error loc "fpu takes exactly three or four arguments"
      in

      ( Stmt.Fpu
          {
            fpu_ref = ref_expr;
            fpu_field = field_qual_ident;
            fpu_old_val = old_val_expr;
            fpu_new_val = new_val_expr;
          },
        disam_tbl )
  | _ when QualIdent.(qual_ident = QualIdent.from_ident Predefs.bindAU_ident) ->
      (* bindAU *)
      begin match (args, assign_lhs) with
      | [], [ token_qual_ident ] ->
          let* proc_qual_ident = Rewriter.current_scope_id in
          let* token = Rewriter.find_and_reify_var token_qual_ident in
          let token_expr = Expr.mk_var ~typ:token.var_decl.var_type token_qual_ident in
          let+ _ = ExprTyping.check token_expr (Type.atomic_token proc_qual_ident) in
          (* TODO: check type Type.atomic_token *)
          (Stmt.AUAction { auaction_kind = BindAU token_qual_ident }, disam_tbl)
      | _ -> Error.type_error loc "bindAU takes no arguments"
      end
  | token :: args ->
      let* token =
        disambiguate_and_check_expr token (Type.any |> Type.set_ghost true) disam_tbl
      in
      let* proc_qual_ident =
        match Expr.to_type token with
        | App (AtomicToken proc_qual_ident, [], _) ->
            let+ proc_qual_ident = Rewriter.resolve proc_qual_ident in
            proc_qual_ident
        | typ ->
            type_mismatch_error (Expr.to_loc token)
              (Type.atomic_token (Ident.make Loc.dummy "?" 0 |> QualIdent.from_ident))
              typ
      in

      let* proc_call_decl =
        let+ proc_callable = Rewriter.find_and_reify_callable proc_qual_ident in
        proc_callable.call_decl
      in

      let* proc_args =
        let proc_concrete_in_args =
          List.filter proc_call_decl.call_decl_formals ~f:(fun var_decl ->
              not var_decl.var_implicit)
        in

        let in_args_supplied =
          begin match args with
          | in_args :: []
            when QualIdent.(
                   qual_ident = from_ident Predefs.openAU_ident
                   || qual_ident = from_ident Predefs.abortAU_ident) ->
              true
          | [ in_args; ret ]
            when QualIdent.(qual_ident = from_ident Predefs.commitAU_ident) ->
              true
          | []
            when QualIdent.(
                   qual_ident = from_ident Predefs.openAU_ident
                   || qual_ident = from_ident Predefs.abortAU_ident) ->
              false
          | ret :: [] when QualIdent.(qual_ident = from_ident Predefs.commitAU_ident) ->
              false
          | _ ->
              Error.type_error loc
                "Incorrect number of arguments supplied to AU operator."
          end
        in

        match in_args_supplied with
        | true ->
            let in_args_tuple = List.hd_exn args in

            let tuple_tp =
              Type.mk_prod loc
                (List.map proc_concrete_in_args ~f:(fun arg_var_decl ->
                     arg_var_decl.var_type))
              |> Type.set_ghost true
            in

            let* in_args_tuple =
              disambiguate_and_check_expr in_args_tuple tuple_tp disam_tbl
            in
            let in_args = Expr.unfold_tuple in_args_tuple in
            Rewriter.return in_args
        | false ->
            let* curr_callable_qi = Rewriter.current_scope_id in
            if QualIdent.(proc_qual_ident = curr_callable_qi) then
              let curr_callable_concrete_args =
                List.filter call_decl.call_decl_formals ~f:(fun var_decl ->
                    not var_decl.var_implicit)
              in

              let+ curr_callable_concrete_arg_exprs =
                Rewriter.List.map curr_callable_concrete_args ~f:(fun arg ->
                    let+ var_def =
                      Rewriter.find_and_reify_var (QualIdent.from_ident arg.var_name)
                    in
                    Expr.from_var_decl var_def.var_decl)
              in
              curr_callable_concrete_arg_exprs
            else
              Error.type_error loc
                "Incorrect number of arguments supplied to AU operator; expected in-args \
                 (as a single tuple) since another procedure's atomicToken is being \
                 manipulated."
      in
      (* openAU *)
      if QualIdent.(qual_ident = QualIdent.from_ident Predefs.openAU_ident) then
        let implicit_vars =
          Base.List.map2_exn assign_lhs var_decls_lhs ~f:(fun qual_ident var_decl ->
              Expr.mk_var ~typ:var_decl.var_type qual_ident)
        in
        let implicit_expected_types =
          Base.List.filter_map proc_call_decl.call_decl_formals ~f:(fun var_decl ->
              if var_decl.var_implicit then Some var_decl.var_type else None)
        in
        if List.(not (length implicit_expected_types = length implicit_vars)) then
          Error.type_error loc
            (Printf.sprintf
               !"Incorrect number of implicit arguments supplied on LHS for %{QualIdent}"
               proc_qual_ident)
        else
          let args = Expr.mk_tuple ~loc implicit_vars in
          let+ _ =
            ExprTyping.check args
              (Type.mk_prod loc implicit_expected_types |> Type.set_ghost true)
          in
          ( Stmt.AUAction
              {
                auaction_kind =
                  OpenAU
                    { token; proc_qi = proc_qual_ident; proc_args; lhs = implicit_vars };
              },
            disam_tbl )
      else if QualIdent.(qual_ident = QualIdent.from_ident Predefs.commitAU_ident) then
        (* commitAU *)
        let returns_tuple = List.last_exn args in
        let* returns =
          Rewriter.List.map (Expr.unfold_tuple returns_tuple) ~f:(fun e ->
              disambiguate_expr e disam_tbl)
        in
        let* proc =
          Rewriter.find_and_reify_callable proc_qual_ident |+> fun c -> c.call_decl
        in
        let* () =
          Rewriter.Logs.debug (fun printers m ->
              m "StmtTyping.check_au_action: commitAU: returns = [ %a ]"
                printers.pr_expr_list returns)
        in
        let+ returns =
          ExprTyping.check_returns loc ~is_ghost_scope:true ~is_call:false proc returns
        in
        ( Stmt.AUAction
            { auaction_kind = CommitAU { token; proc_args; proc_rets = returns } },
          disam_tbl )
      else if QualIdent.(qual_ident = QualIdent.from_ident Predefs.abortAU_ident) then
        (* abortAU *)
        Rewriter.return
          (Stmt.AUAction { auaction_kind = AbortAU { token; proc_args } }, disam_tbl)
      else
        Error.type_error loc
          (Printf.sprintf
             !"'%{QualIdent}' is not a recognized atomic-update (AU) action (expected \
               one of bindAU, openAU, commitAU, abortAU, ...)"
             qual_ident)
  | _ ->
      Error.type_error loc
        (Printf.sprintf !"%{QualIdent} expects at least one argument" qual_ident)

let rec check_basic call_decl (basic_stmt : Stmt.basic_stmt_desc) (stmt_loc : Loc.t)
    (disam_tbl : DisambiguationTbl.t) : (Stmt.basic_stmt_desc * DisambiguationTbl.t) t =
  let open Rewriter.Syntax in
  let* is_ghost_scope = Rewriter.is_ghost_scope in
  let get_assign_lhs ~is_init ?(is_ghost_cmd = false) orig_qual_ident =
    let* qual_ident = disambiguate_ident orig_qual_ident disam_tbl in
    let* qual_ident, symbol = Rewriter.resolve_and_find qual_ident in
    let+ symbol = Rewriter.Symbol.reify symbol in
    match symbol with
    | VarDef { var_decl; _ }
      when (is_ghost_scope || is_ghost_cmd) && not var_decl.var_ghost ->
        Error.type_error (QualIdent.to_loc qual_ident)
          (Printf.sprintf
             !"Cannot assign to non-ghost var %{QualIdent} in ghost context"
             orig_qual_ident)
    | VarDef { var_decl; _ } when (not var_decl.var_const) || is_init ->
        (qual_ident, var_decl)
    | _ ->
        Error.type_error (QualIdent.to_loc qual_ident)
          (Printf.sprintf
             !"Cannot assign to %s %{QualIdent}"
             (Symbol.kind symbol) orig_qual_ident)
  in
  let ext_stmt_functs =
    {
      ExtApi.get_assign_lhs =
        (fun ~is_init ?is_ghost_cmd qi ->
          run_typing (get_assign_lhs ~is_init ?is_ghost_cmd qi));
      expand_type_expr = (fun tp -> run_typing (TypeExpr.expand_type_expr tp));
      disambiguate_and_check_expr =
        (fun e exp d -> run_typing (disambiguate_and_check_expr e exp d));
      type_mismatch_error;
      disam_tbl_add_var_decl = DisambiguationTbl.add_var_decl;
      check_symbol = !Rewriter.check_symbol_ref;
      check_stmt = !Rewriter.check_stmt_ref;
    }
  in
  (* Whether the type of [expr], an operand the core indexes, is one the core's
       lookup and update apply to. *)
  let peek_core_indexable (expr : expr) : bool t =
    let* expr =
      disambiguate_and_check_expr expr (Type.any |> Type.set_ghost true) disam_tbl
    in
    let+ typ = TypeExpr.expand_type_expr (Expr.to_type expr) in
    ExprTyping.is_core_indexable typ
  in
  (* Offers [basic_stmt], which the core rejects, to the extensions. *)
  let claim_stmt (basic_stmt : Stmt.basic_stmt_desc) =
    let* ext_hooks = Rewriter.current_ext_hooks in
    let* claim =
      lift (ext_hooks.claim_basic_stmt basic_stmt stmt_loc disam_tbl ext_stmt_functs)
    in
    match claim with
    | None -> Rewriter.return None
    | Some ext_stmt ->
        let+ res = check_basic call_decl (BasicStmtExt ext_stmt) stmt_loc disam_tbl in
        Some res
  in
  (* Offers [basic_stmt] to the extensions if [expr], its right-hand side or
       initializer, is a lookup or update whose map operand is not of map type. *)
  let claim_if_not_core_indexed (expr : expr) =
    match expr with
    | App ((MapLookUp | MapUpdate), base :: _, _) ->
        let* core_indexable = peek_core_indexable base in
        if core_indexable then Rewriter.return None else claim_stmt basic_stmt
    | _ -> Rewriter.return None
  in
  match basic_stmt with
  | VarDef var_def ->
      let* claimed =
        match var_def.var_init with
        | Some init -> claim_if_not_core_indexed init
        | None -> Rewriter.return None
      in
      begin match claimed with
      | Some res -> Rewriter.return res
      | None ->
          let* var_decl = TypeExpr.check_var_decl var_def.var_decl in
          let* curr_callable = Rewriter.current_scope_id in
          let var_ghost = var_decl.var_ghost || is_ghost_scope in
          let* var_type =
            match var_def.var_init with
            | None -> Rewriter.return var_decl.var_type
            | Some (App (Var qual_ident, _, _))
              when Predefs.is_qual_ident_au_cmnd qual_ident ->
                Rewriter.return
                @@
                if Ident.(Predefs.bindAU_ident = QualIdent.unqualify qual_ident) then
                  Type.mk_atomic_token (QualIdent.to_loc qual_ident) curr_callable
                else Type.meet var_decl.var_type Type.any
            | Some (App (Read, [ expr1; field_expr ], _)) ->
                let field_qual_ident = Expr.to_qual_ident field_expr in
                let* _, symbol =
                  (* `e.M.value` for an uninstantiated functor `M` (see
                     [ImplicitInstantiation.try_resolve_implicit_instantiation_destr]). An
                     unqualified field or destructor imported from one is recovered as in
                     [ExprTyping]'s [Read] case: the deferred import first, then the type
                     of `e`. *)
                  ImplicitInstantiation.resolve_or_implicit field_qual_ident
                    ~on_miss:(fun () ->
                      let* imported = Rewriter.find_import_target field_qual_ident in
                      let candidate =
                        Base.Option.value imported ~default:field_qual_ident
                      in
                      let* peeked_expr1 =
                        disambiguate_and_check_expr expr1
                          (Type.any |> Type.set_ghost var_ghost)
                          disam_tbl
                      in
                      ImplicitInstantiation.try_resolve_implicit_instantiation_destr
                        ~field_ident:candidate ~arg_typ:(Expr.to_type peeked_expr1))
                in
                let+ symbol = Rewriter.Symbol.reify symbol in
                begin match symbol with
                | FieldDef { field_type = App (Fld, [ typ ], _); _ } -> typ
                | DestrDef destr_def -> destr_def.destr_return_type
                | _ -> Type.meet var_decl.var_type Type.any
                end
            | Some expr ->
                let+ expr =
                  disambiguate_and_check_expr expr
                    (var_decl.var_type |> Type.set_ghost var_ghost)
                    disam_tbl ~allow_proc_call:true
                in
                Expr.to_type expr
          in
          let var_decl =
            if not (Type.equal var_type Type.any) then
              { var_decl with var_type = var_type |> Type.set_ghost var_ghost; var_ghost }
            else
              Error.error var_decl.var_loc
              @@ Printf.sprintf "Type annotation missing for variable %s"
                   (Ident.to_string var_decl.var_name)
          in
          let var_decl, disam_tbl' = DisambiguationTbl.add_var_decl var_decl disam_tbl in
          let* _ =
            Rewriter.introduce_symbol
              (VarDef { var_decl; var_init = None; var_is_free = NotFree })
          in
          let var = QualIdent.from_ident var_decl.var_name in
          Rewriter.return
          @@ (Stmt.Havoc { havoc_var = var; havoc_is_init = true }, disam_tbl')
      end
  | Spec (sk, spec) ->
      let+ spec = check_spec disam_tbl spec in
      (Stmt.Spec (sk, spec), disam_tbl)
  | Assign assign_desc -> begin
      let* claimed = claim_if_not_core_indexed assign_desc.assign_rhs in
      match claimed with
      | Some res -> Rewriter.return res
      | None -> (
          let* assign_lhs, var_decls_lhs =
            Rewriter.List.fold_right assign_desc.assign_lhs ~init:([], [])
              ~f:(fun orig_qual_ident (assign_lhs, var_decls_lhs) ->
                let+ qual_ident, var_decl =
                  get_assign_lhs orig_qual_ident ~is_init:assign_desc.assign_is_init
                in
                (qual_ident :: assign_lhs, var_decl :: var_decls_lhs))
          in

          (* The assignment is ghost if all targets are ghost or the scope is ghost. With
             both ghost and non-ghost targets, it is not, so that the non-ghost ones are
             checked against a non-ghost type. *)
          let is_ghost_assign =
            is_ghost_scope || List.for_all var_decls_lhs ~f:(fun var -> var.var_ghost)
          in

          match assign_desc.assign_rhs with
          (* Field read *)
          | App (Read, [ ref_expr; read_expr ], _) ->
              let read_expr_qi = Expr.to_qual_ident read_expr in

              let* read_expr_qi, read_symbol =
                (* `ref_expr.M.value` for an uninstantiated functor `M`, or an unqualified
                   field or destructor imported from one: recovered as in [ExprTyping]'s
                   [Read] case. *)
                ImplicitInstantiation.resolve_or_implicit read_expr_qi ~on_miss:(fun () ->
                    let* imported = Rewriter.find_import_target read_expr_qi in
                    let candidate = Base.Option.value imported ~default:read_expr_qi in
                    let* peeked_ref_expr =
                      disambiguate_and_check_expr ref_expr
                        (Type.any |> Type.set_ghost is_ghost_assign)
                        disam_tbl
                    in
                    ImplicitInstantiation.try_resolve_implicit_instantiation_destr
                      ~field_ident:candidate
                      ~arg_typ:(Expr.to_type peeked_ref_expr))
              in
              let* read_symbol = Rewriter.Symbol.reify read_symbol in

              begin match read_symbol with
              | FieldDef f ->
                  let* () =
                    Rewriter.Logs.debug (fun printers m ->
                        m "StmtTyping.check: read_assign_rhs: %a" printers.pr_expr
                          assign_desc.assign_rhs)
                  in
                  let field_qual_ident = read_expr_qi in
                  let field_read_lhs =
                    match assign_desc.assign_lhs with
                    | [ lhs ] -> lhs
                    | _ ->
                        Error.type_error stmt_loc
                          "Expected exactly one variable on left-hand side of field read"
                  in

                  let field_read_desc =
                    Stmt.
                      {
                        field_read_lhs;
                        field_read_field = field_qual_ident;
                        field_read_ref = ref_expr;
                        field_read_is_init = assign_desc.assign_is_init;
                      }
                  in
                  check_basic call_decl (Stmt.FieldRead field_read_desc) stmt_loc
                    disam_tbl
              | DestrDef destr_def ->
                  let assign_rhs =
                    Expr.mk_app ~loc:stmt_loc ~typ:destr_def.destr_return_type
                      (Expr.DataDestr read_expr_qi) [ ref_expr ]
                  in
                  check_basic call_decl
                    (Stmt.Assign { assign_desc with assign_rhs })
                    stmt_loc disam_tbl
              | _ ->
                  Error.type_error stmt_loc
                    (Printf.sprintf
                       "Expected a data destructor on the right-hand side of this field \
                        read, but found %s"
                       (Symbol.kind read_symbol))
              end
          (* AU action *)
          | App (Var qual_ident, args, _) when Predefs.is_qual_ident_au_cmnd qual_ident ->
              check_au_action call_decl assign_lhs var_decls_lhs qual_ident args stmt_loc
                disam_tbl
          | _ -> (
              let* () =
                Rewriter.Logs.debug (fun printers m ->
                    m "StmtTyping.check: assign_desc: %a" printers.pr_stmt_basic
                      (Assign assign_desc))
              in

              let* assign_rhs_callable_opt =
                match assign_desc.assign_rhs with
                | App (Var qual_ident, args, _) -> (
                    let* qual_ident = disambiguate_ident qual_ident disam_tbl in
                    (* Whether the right-hand side is a call of a procedure or lemma,
                       without an error if it does not resolve: `M.foo` may resolve
                       through implicit instantiation. Otherwise, it is typed as an
                       expression. *)
                    let* resolved =
                      ImplicitInstantiation.resolve_or_implicit_opt qual_ident
                        ~on_miss:(fun () ->
                          (* `args` needs disambiguating here since try_resolve_implicit_instantiation's
                       argument peek doesn't disambiguate local identifiers itself. *)
                          let* args =
                            Rewriter.List.map args ~f:(fun e ->
                                disambiguate_expr e disam_tbl)
                          in
                          (* As in the expression path: an unqualified name imported from an
                       uninstantiated functor carries no functor path of its own. *)
                          let* imported = Rewriter.find_import_target qual_ident in
                          let candidate =
                            Base.Option.value imported ~default:qual_ident
                          in
                          (* Only a callable becomes a [Stmt.Call]; anything else, such as
                             a constructor `nil`, is typed as an expression, against the
                             type of the left-hand side. *)
                          ImplicitInstantiation.try_resolve_implicit_instantiation
                            ~check_expr:ExprTyping.check
                            ~claimed_location:ExprTyping.claimed_location ~loc:stmt_loc
                            ~qual_ident:candidate ~arg_exprs:args ~only_calls:true
                            ~expected_typ:(Type.any |> Type.set_ghost is_ghost_scope)
                            ())
                    in
                    match resolved with
                    | None -> Rewriter.return None
                    | Some (qual_ident, symbol) -> (
                        let+ symbol = Rewriter.Symbol.reify symbol in
                        match symbol with
                        | CallDef call_def -> Some (symbol, qual_ident, args)
                        | _ -> None))
                | _ -> Rewriter.return None
              in

              match assign_rhs_callable_opt with
              | Some (symbol, proc_qual_ident, args) -> begin
                  Logs.debug (fun m ->
                      m "StmtTyping.check: assign_rhs_qual_ident: %a; %b" QualIdent.pr
                        proc_qual_ident
                        QualIdent.(
                          proc_qual_ident = QualIdent.from_ident Predefs.bindAU_ident));

                  let (call_desc : Stmt.call_desc) =
                    {
                      call_lhs = assign_desc.assign_lhs;
                      call_name = proc_qual_ident;
                      call_args = args;
                      call_is_spawn = false;
                      call_is_init = assign_desc.assign_is_init;
                    }
                  in
                  check_basic call_decl (Stmt.Call call_desc) stmt_loc disam_tbl
                  (*(Stmt.Call call_desc, disam_tbl)*)
                end
              | None ->
                  let expected_type =
                    Type.mk_prod
                      (Expr.to_loc assign_desc.assign_rhs)
                      (List.map var_decls_lhs ~f:(fun var -> var.var_type))
                    |> fun ty -> if is_ghost_assign then ty |> Type.set_ghost true else ty
                  in
                  let* assign_rhs =
                    disambiguate_and_check_expr assign_desc.assign_rhs expected_type
                      disam_tbl
                  in

                  let* () =
                    Rewriter.Logs.debug (fun printers m ->
                        m "StmtTyping.check: disam_assign_rhs: %a" printers.pr_expr
                          assign_rhs)
                  in

                  let assign_desc = Stmt.{ assign_desc with assign_lhs; assign_rhs } in
                  Rewriter.return (Stmt.Assign assign_desc, disam_tbl)))
    end
  | Bind bind_desc ->
      let* bind_lhs, _ =
        Rewriter.List.fold_right bind_desc.bind_lhs ~init:([], [])
          ~f:(fun orig_qual_ident (assign_lhs, var_decls_lhs) ->
            let+ qual_ident, var_decl =
              get_assign_lhs orig_qual_ident ~is_ghost_cmd:true ~is_init:false
            in
            (qual_ident :: assign_lhs, var_decl :: var_decls_lhs))
      in
      let+ spec_form =
        disambiguate_and_check_expr bind_desc.bind_rhs.spec_form
          (Type.any |> Type.set_ghost true)
          disam_tbl
      in
      let bind_rhs = { bind_desc.bind_rhs with spec_form } in
      let bind_desc = Stmt.{ bind_lhs; bind_rhs } in
      (Stmt.Bind bind_desc, disam_tbl)
  | FieldWrite fw_desc ->
      let* field_write_field, symbol =
        Rewriter.resolve_and_find fw_desc.field_write_field
      in
      let* symbol = Rewriter.Symbol.reify symbol in
      let field_type =
        match symbol with
        | FieldDef { field_type = App (Fld, [ field_type ], _); field_is_ghost; _ } ->
            if is_ghost_scope && not field_is_ghost then
              Error.type_error
                (QualIdent.to_loc fw_desc.field_write_field)
                (Printf.sprintf
                   !"Cannot assign to non-ghost field %{QualIdent} in ghost context"
                   fw_desc.field_write_field)
            else field_type
        | _ ->
            Error.type_error (QualIdent.to_loc fw_desc.field_write_field) "Expected field"
      in
      let* is_field_an_ra = lift (ProgUtils.is_ra_type field_type) in
      let _ =
        if is_field_an_ra then
          Error.type_error stmt_loc
            (Printf.sprintf
               !"Cannot assign directly to field %{QualIdent}, whose value is a resource \
                 algebra (RA) element; use a frame-preserving update ('fpu') instead"
               fw_desc.field_write_field)
      in
      let* field_write_ref =
        disambiguate_and_check_expr fw_desc.field_write_ref
          (Type.ref |> Type.set_ghost is_ghost_scope)
          disam_tbl
      in
      let+ field_write_val =
        disambiguate_and_check_expr fw_desc.field_write_val field_type disam_tbl
      in
      (Stmt.FieldWrite { field_write_ref; field_write_field; field_write_val }, disam_tbl)
  | FieldRead fr_desc ->
      let* fr_var_qual_ident, var_decl =
        get_assign_lhs fr_desc.field_read_lhs ~is_init:fr_desc.field_read_is_init
      in
      let* fr_type = TypeExpr.expand_type_expr var_decl.var_type in
      let* field_read_ref, field_read_field, field_type, symbol =
        disambiguate_and_check_field_read fr_desc.field_read_ref fr_desc.field_read_field
          disam_tbl
      in
      begin match symbol with
      | DestrDef { destr_return_type; _ } ->
          let rhs_loc =
            Loc.merge (Expr.to_loc field_read_ref) (QualIdent.to_loc field_read_field)
          in
          let assign_rhs =
            Expr.mk_app ~loc:rhs_loc ~typ:destr_return_type
              (DataDestr fr_desc.field_read_field) [ fr_desc.field_read_ref ]
          in
          let assign_desc =
            Stmt.
              {
                assign_lhs = [ fr_desc.field_read_lhs ];
                assign_rhs;
                assign_is_init = fr_desc.field_read_is_init;
              }
          in
          check_basic call_decl (Stmt.Assign assign_desc) stmt_loc disam_tbl
      | _ ->
          let+ _ =
            ExprTyping.set_checked_type
              (Expr.mk_var ~typ:fr_type fr_var_qual_ident)
              fr_type field_type
              (field_type |> Type.set_ghost_to fr_type)
          in
          let field_read_desc =
            Stmt.
              {
                fr_desc with
                field_read_lhs = fr_var_qual_ident;
                field_read_field;
                field_read_ref;
              }
          in
          (Stmt.FieldRead field_read_desc, disam_tbl)
      end
  | Havoc hvc ->
      let+ havoc_var, _ = get_assign_lhs hvc.havoc_var ~is_init:hvc.havoc_is_init in
      (Stmt.Havoc { hvc with havoc_var }, disam_tbl)
  | Return expr ->
      if is_ghost_scope && Poly.(call_decl.Callable.call_decl_kind = Proc) then
        Error.type_error stmt_loc "Cannot return in a ghost block";

      let* expr = disambiguate_expr expr disam_tbl in
      let return_list = Expr.unfold_tuple expr in

      let+ return_list =
        ExprTyping.check_returns stmt_loc ~is_ghost_scope ~is_call:false call_decl
          return_list
      in
      let expr = Expr.mk_tuple ~loc:(Expr.to_loc expr) return_list in
      (Stmt.Return expr, disam_tbl)
  | Use use_desc ->
      let* use_name, symbol =
        let* id = disambiguate_ident use_desc.use_name disam_tbl in
        (* `fold M.p(x)` for an uninstantiated functor `M`, or `fold p(x)` with `p`
           imported from one: the instance is inferred from the arguments, as for
           `M.p`. *)
        ImplicitInstantiation.resolve_or_implicit id ~on_miss:(fun () ->
            let* args =
              Rewriter.List.map use_desc.use_args ~f:(fun e ->
                  disambiguate_expr e disam_tbl)
            in
            let* imported = Rewriter.find_import_target id in
            let candidate = Base.Option.value imported ~default:id in
            ImplicitInstantiation.try_resolve_implicit_instantiation
              ~check_expr:ExprTyping.check ~claimed_location:ExprTyping.claimed_location
              ~loc:stmt_loc ~qual_ident:candidate ~arg_exprs:args ~only_calls:true
              ~expected_typ:(Type.perm |> Type.set_ghost true)
              ())
      in
      let* symbol = Rewriter.Symbol.reify symbol in

      let pred_decl, pred_def =
        match symbol with
        | CallDef
            {
              call_decl = { call_decl_kind = Pred; _ } as pred_decl;
              call_def = FuncDef { func_body = pred_def };
            } ->
            (pred_decl, pred_def)
        | CallDef
            {
              call_decl = { call_decl_kind = Invariant; _ } as pred_decl;
              call_def = FuncDef { func_body = pred_def };
            } ->
            (pred_decl, pred_def)
        | _ ->
            Error.type_error stmt_loc
              ("Expected predicate or invariant identifier, but found "
             ^ QualIdent.to_string use_name)
      in

      let exists_vars =
        Option.value pred_def ~default:(Expr.mk_unit Loc.dummy)
        |> Expr.existential_vars_type
      in
      let find_type ident : type_expr t =
        let ty_opt =
          Map.fold exists_vars ~init:None ~f:(fun ~key ~data acc ->
              if Option.is_none acc && String.(Ident.name ident = Ident.name key) then
                Some data
              else acc)
        in
        match ty_opt with
        | Some ty -> TypeExpr.check ty
        | _ ->
            Error.type_error (Ident.to_loc ident)
              (Printf.sprintf
                 !"Could not find existential variable %{Ident} in %s %{QualIdent}"
                 ident (Symbol.kind symbol) use_desc.use_name)
      in

      let* use_args =
        Rewriter.List.map use_desc.use_args ~f:(fun expr ->
            disambiguate_expr expr disam_tbl)
      in

      let* use_args = ExprTyping.check_args stmt_loc true pred_decl use_args in

      let+ use_witnesses_or_binds =
        Rewriter.List.map use_desc.use_witnesses_or_binds ~f:(fun (i, e) ->
            match use_desc.use_kind with
            | Fold ->
                let* ty = find_type i in
                let+ e =
                  disambiguate_and_check_expr e (ty |> Type.set_ghost true) disam_tbl
                in
                (i, e)
            | Unfold -> (
                match e with
                | App (Var qual_ident, [], _) when QualIdent.is_local qual_ident ->
                    let* ty = find_type (QualIdent.unqualify qual_ident) in
                    let+ ie =
                      disambiguate_and_check_expr
                        (Expr.mk_var
                           ~typ:(Type.mk_any (Ident.to_loc i))
                           (QualIdent.from_ident i))
                        (ty |> Type.set_ghost true)
                        disam_tbl
                    in
                    (Expr.to_ident ie, e)
                | _ -> Error.type_error (Expr.to_loc e) "Expected local identifier"))
      in

      (Stmt.Use { use_desc with use_name; use_args; use_witnesses_or_binds }, disam_tbl)
  | New new_desc ->
      let* new_qual_ident, var_decl =
        get_assign_lhs new_desc.new_lhs ~is_init:new_desc.new_is_init
      in
      let* var_type_expanded = TypeExpr.expand_type_expr var_decl.var_type in

      (* A ghost `new`, of a ghost variable or in a ghost scope, may initialize only ghost
         fields. A declaration with `new` becomes two statements, so the ghost scope alone
         does not show it. *)
      let is_ghost_new = var_decl.var_ghost || is_ghost_scope in
      if Type.equal var_type_expanded Type.ref then
        let check_field_init (field_name, expr_opt) =
          let* field_name, symbol = Rewriter.resolve_and_find field_name in
          let* () =
            match Rewriter.Symbol.orig_symbol symbol with
            | FieldDef { field_is_ghost; _ } ->
                if is_ghost_new && not field_is_ghost then
                  Error.type_error (QualIdent.to_loc field_name)
                    (Printf.sprintf
                       !"Cannot assign to non-ghost field %{QualIdent} in ghost context"
                       field_name)
                else Rewriter.return ()
            | _ -> Error.type_error (QualIdent.to_loc field_name) "Expected field"
          in
          let* field_type = Rewriter.Symbol.reify_field_type stmt_loc symbol in
          let+ expr_opt =
            Rewriter.Option.map expr_opt ~f:(fun expr ->
                disambiguate_and_check_expr expr field_type disam_tbl)
          in
          (field_name, expr_opt)
        in
        let+ new_args = Rewriter.List.map new_desc.new_args ~f:check_field_init in

        let new_desc = Stmt.{ new_desc with new_lhs = new_qual_ident; new_args } in

        (Stmt.New new_desc, disam_tbl)
      else type_mismatch_error stmt_loc Type.ref var_decl.var_type
      (* The parser produces assignments for these, which this function turns into the
         constructs. They occur here because [Typing.check_symbol] is also applied to
         symbols built by later passes. *)
  | Call call_desc -> (
      let* call_lhs, var_decls_lhs =
        Rewriter.List.fold_right call_desc.call_lhs ~init:([], [])
          ~f:(fun orig_qual_ident (assign_lhs, var_decls_lhs) ->
            let+ qual_ident, var_decl =
              get_assign_lhs orig_qual_ident ~is_init:call_desc.call_is_init
            in
            (qual_ident :: assign_lhs, var_decl :: var_decls_lhs))
      in
      let* call_lhs_expr =
        Rewriter.List.map2_exn call_lhs var_decls_lhs ~f:(fun qual_ident var_decl ->
            let+ typ = TypeExpr.expand_type_expr var_decl.var_type in
            Expr.mk_var ~typ qual_ident)
      in

      let* call_decl =
        Rewriter.find_and_reify_callable call_desc.call_name |+> fun c -> c.call_decl
      in
      let* call_lhs_expr =
        ExprTyping.check_returns stmt_loc ~is_ghost_scope ~is_call:true call_decl
          call_lhs_expr
      in
      let is_ghost =
        is_ghost_scope
        ||
        match call_decl.call_decl_kind with
        | Lemma -> true
        | Func ->
            List.for_all call_lhs_expr ~f:(fun e -> e |> Expr.to_type |> Type.is_ghost)
        | _ -> false
      in
      let* _ = Rewriter.enter_ghost is_ghost in
      let* call_expr =
        Expr.App
          (Var call_desc.call_name, call_desc.call_args, Expr.mk_attr stmt_loc Type.any)
        |> fun expr ->
        disambiguate_and_check_expr expr
          (Type.any |> Type.set_ghost is_ghost)
          disam_tbl ~allow_proc_call:true
      in
      let+ _ = Rewriter.exit_ghost in

      match call_expr with
      | App (Var call_name, call_args, _expr_attr) ->
          let call_desc = { call_desc with call_lhs; call_name; call_args } in
          (Stmt.Call call_desc, disam_tbl)
      | _ -> failwith "Unexpected error during type checking.")
  | AUAction _au_action_kind ->
      internal_error stmt_loc "Did not expect AU action stmts in AST at this stage."
  | Fpu fpu_desc ->
      let open Rewriter.Syntax in
      (* Process reference expression as ghost ref *)
      let* fpu_ref =
        disambiguate_and_check_expr fpu_desc.fpu_ref
          (Type.ref |> Type.set_ghost true)
          disam_tbl
      in

      (* Resolve field and check it is a ghost Fld field with element type *)
      let* fpu_field, symbol = Rewriter.resolve_and_find fpu_desc.fpu_field in
      let* symbol = Rewriter.Symbol.reify symbol in
      let* given_type =
        match symbol with
        | FieldDef field_decl -> (
            match field_decl.field_type with
            | App (Fld, [ elem_ty ], _) ->
                if not field_decl.field_is_ghost then
                  Error.type_error
                    (QualIdent.to_loc fpu_desc.fpu_field)
                    "Frame-preserving updates are only allowed on ghost fields"
                else Rewriter.return elem_ty
            | _ ->
                Error.type_error
                  (QualIdent.to_loc fpu_desc.fpu_field)
                  "Expected field identifier")
        | _ ->
            Error.type_error
              (QualIdent.to_loc fpu_desc.fpu_field)
              "Expected field identifier"
      in

      (* Process optional old value and mandatory new value at the field element type *)
      let* fpu_old_val =
        Rewriter.Option.map fpu_desc.fpu_old_val ~f:(fun e ->
            disambiguate_and_check_expr e given_type disam_tbl)
      in
      let+ fpu_new_val =
        disambiguate_and_check_expr fpu_desc.fpu_new_val given_type disam_tbl
      in

      (Stmt.Fpu { fpu_ref; fpu_field; fpu_old_val; fpu_new_val }, disam_tbl)
  | BasicStmtExt (stmt_ext, expr_list) ->
      let* ext_hooks = Rewriter.current_ext_hooks in
      lift
        (ext_hooks.type_check_basic_stmt call_decl stmt_ext expr_list stmt_loc disam_tbl
           ext_stmt_functs)

let check ?(new_scope = true) call_decl (stmt : Stmt.t) (disam_tbl : DisambiguationTbl.t)
    : (Stmt.t * DisambiguationTbl.t) t =
  let rec check ?(new_scope = true) stmt disam_tbl =
    let open Rewriter.Syntax in
    let* () =
      Rewriter.Logs.debug (fun printers m ->
          m "StmtTyping.check: %a" printers.pr_stmt stmt)
    in
    let* is_ghost_scope = Rewriter.is_ghost_scope in
    let+ stmt_desc, disam_tbl =
      match stmt.Stmt.stmt_desc with
      | Basic basic_stmt ->
          let+ basic_stmt, disam_tbl' =
            check_basic call_decl basic_stmt (Stmt.to_loc stmt) disam_tbl
          in
          (Stmt.Basic basic_stmt, disam_tbl')
      | Block block_desc ->
          let* () = Rewriter.enter_block block_desc in
          let disam_tbl =
            if new_scope then DisambiguationTbl.push disam_tbl else disam_tbl
          in

          let* disam_tbl, stmt_list =
            Rewriter.List.fold_map block_desc.block_body ~init:disam_tbl
              ~f:(fun disam_tbl stmt ->
                let+ stmt, disam_tbl = check stmt disam_tbl in
                (disam_tbl, stmt))
          in

          let disam_tbl =
            if new_scope then DisambiguationTbl.pop disam_tbl else disam_tbl
          in
          let+ () = Rewriter.exit_block in

          (Stmt.Block { block_desc with block_body = stmt_list }, disam_tbl)
      | Loop loop_desc ->
          let* loop_contract =
            Rewriter.List.map loop_desc.loop_contract ~f:(check_spec disam_tbl)
          in

          let* loop_contract_ext =
            let* ext_hooks = Rewriter.current_ext_hooks in
            Rewriter.List.map loop_desc.loop_contract_ext ~f:(fun contract_ext ->
                lift
                  (ext_hooks.type_check_contract_ext call_decl contract_ext
                     (Stmt.to_loc stmt) disam_tbl
                     {
                       ExtApi.get_assign_lhs =
                         (fun ~is_init:_ ?is_ghost_cmd:_ qi _state ->
                           Error.internal_error (QualIdent.to_loc qi)
                             "assignments are not permitted in a contract clause");
                       expand_type_expr =
                         (fun tp -> run_typing (TypeExpr.expand_type_expr tp));
                       disambiguate_and_check_expr =
                         (fun e exp d -> run_typing (disambiguate_and_check_expr e exp d));
                       type_mismatch_error;
                       disam_tbl_add_var_decl = DisambiguationTbl.add_var_decl;
                       check_symbol = !Rewriter.check_symbol_ref;
                       check_stmt =
                         (fun _call_decl stmt _disam_tbl ->
                           Error.internal_error (Stmt.to_loc stmt)
                             "statements are not permitted in a contract clause");
                     }))
          in

          let disam_tbl = DisambiguationTbl.push disam_tbl in
          let* loop_prebody, disam_tbl = check loop_desc.loop_prebody disam_tbl in
          let disam_tbl = DisambiguationTbl.pop disam_tbl in

          let* loop_test =
            disambiguate_and_check_expr loop_desc.loop_test
              (Type.bool |> Type.set_ghost is_ghost_scope)
              disam_tbl
          in

          let disam_tbl = DisambiguationTbl.push disam_tbl in
          let+ loop_postbody, disam_tbl = check loop_desc.loop_postbody disam_tbl in
          let disam_tbl = DisambiguationTbl.pop disam_tbl in

          (* Actually think about what variables need to be collected in `locals`. What if same variable is declared in multiple scopes in a callable, do all of them go in the `call_decl.call_decl_locals`? TW: I would say yes, unless you already have that information in the SymbolTable and always lookup locals through that. *)
          let (loop_desc : Stmt.loop_desc) =
            { loop_contract; loop_contract_ext; loop_prebody; loop_test; loop_postbody }
          in

          (Stmt.Loop loop_desc, disam_tbl)
      | Cond cond_desc ->
          let* cond_test =
            Rewriter.Option.map
              ~f:(fun test ->
                disambiguate_and_check_expr test
                  (Type.bool |> Type.set_ghost is_ghost_scope)
                  disam_tbl)
              cond_desc.cond_test
          in

          let disam_tbl = DisambiguationTbl.push disam_tbl in
          let* cond_then, disam_tbl = check cond_desc.cond_then disam_tbl in
          let disam_tbl = DisambiguationTbl.pop disam_tbl in

          let disam_tbl = DisambiguationTbl.push disam_tbl in
          let+ cond_else, disam_tbl = check cond_desc.cond_else disam_tbl in
          let disam_tbl = DisambiguationTbl.pop disam_tbl in

          let (cond_desc : Stmt.cond_desc) =
            { cond_desc with cond_test; cond_then; cond_else }
          in

          (Stmt.Cond cond_desc, disam_tbl)
      | StmtExt stmt_ext ->
          let* ext_hooks = Rewriter.current_ext_hooks in
          lift
            (ext_hooks.type_check_stmt_ext call_decl stmt_ext (Stmt.to_loc stmt) disam_tbl
               {
                 ExtApi.get_assign_lhs =
                   (fun ~is_init:_ ?is_ghost_cmd:_ qi _state ->
                     Error.internal_error (QualIdent.to_loc qi)
                       "assignments are not permitted directly in a top-level statement \
                        extension");
                 expand_type_expr = (fun tp -> run_typing (TypeExpr.expand_type_expr tp));
                 disambiguate_and_check_expr =
                   (fun e exp d -> run_typing (disambiguate_and_check_expr e exp d));
                 type_mismatch_error;
                 disam_tbl_add_var_decl = DisambiguationTbl.add_var_decl;
                 check_symbol = !Rewriter.check_symbol_ref;
                 check_stmt =
                   (fun _call_decl stmt disam_tbl -> run_typing (check stmt disam_tbl));
               })
    in

    (Stmt.{ stmt_desc; stmt_loc = stmt.stmt_loc }, disam_tbl)
  in

  check ~new_scope stmt disam_tbl
