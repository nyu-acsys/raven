(** Computes witnesses and eliminates existential resource assertions. *)

open Base
open Ast
open Ast.Stmt
open Ast.Expr
open Util
open HeapNames

type conditions = Expr.t list
type universal_quants = { univ_vars : (ident * var_decl) list; triggers : expr list list }

let ident_to_skolem_fn_ident ~loc ident =
  Ident.fresh loc ("$skolem_" ^ Ident.to_string ident)

type skolem_function_def = {
  universal_quants : universal_quants;
  var_decl : var_decl;
  preconds : expr list;
  postconds : expr list;
  optn_args : (var_decl * expr) list;
  skolem_fn_id : ident;
  loc : location;
}

(** `generate_skolem_function` generates the symbol for the skolem function to be added.
    These are type-checked and added to the state by `generate_skolem_functions`. *)
let generate_skolem_function (universal_quants : universal_quants) (var_decl : var_decl)
    ?(preconds : expr list = []) ?(postconds : expr list = [])
    ?(optn_args : (var_decl * expr) list = []) ~skolem_id ~loc :
    (Module.symbol * expr) Rewriter.t =
  let open Rewriter.Syntax in
  let univ_quants_list = universal_quants.univ_vars in

  let skolem_fn_ident = skolem_id in

  let* () =
    Rewriter.Logs.debug (fun printers m ->
        m
          "WitnessComputation.generate_skolem_function INIT: skolem_fn_ident: %a \n\
          \ universal_quants: %a \n\
          \ var_decl: %a \n\
          \ preconds: %a \n\
          \ postconds: %a \n\
          \ optn_args: %a \n\
          \ "
          Ident.pr skolem_fn_ident printers.pr_type_var_decl_list
          (List.map ~f:snd universal_quants.univ_vars)
          printers.pr_type_var_decl var_decl printers.pr_expr_list preconds
          printers.pr_expr_list postconds
          (Util.Print.pr_list_comma (fun ppf (vd, e) ->
               Stdlib.Format.fprintf ppf "%a -> %a" printers.pr_type_var_decl vd
                 printers.pr_expr e))
          optn_args)
  in

  let formal_var_decls =
    List.map univ_quants_list ~f:(fun (v, v_decl) ->
        {
          Type.var_name = v_decl.var_name;
          var_loc = loc;
          var_type = v_decl.var_type |> Type.set_ghost true;
          var_const = true;
          var_ghost = true;
          var_implicit = false;
        })
    @ List.map optn_args ~f:(fun (v_decl, _) ->
        {
          Type.var_name = v_decl.var_name;
          var_loc = loc;
          var_type = v_decl.var_type |> Type.set_ghost true;
          var_const = true;
          var_ghost = true;
          var_implicit = false;
        })
  in

  let ret_var_decl =
    {
      Type.var_name = Ident.fresh loc ("ret_" ^ Ident.to_string var_decl.var_name);
      var_loc = loc;
      var_type = var_decl.var_type |> Type.set_ghost true;
      var_const = true;
      var_ghost = true;
      var_implicit = false;
    }
  in

  let preconds, postconds =
    let ret_var_renam_map =
      Map.singleton
        (module QualIdent)
        (QualIdent.from_ident var_decl.var_name)
        (Expr.from_var_decl ret_var_decl)
    in

    ( List.map preconds ~f:(fun precond -> Expr.alpha_renaming precond ret_var_renam_map),
      List.map postconds ~f:(fun postcond ->
          Expr.alpha_renaming postcond ret_var_renam_map) )
  in

  (* Funcs can't carry a `requires` (their contracts must be total), so fold the
     precondition into the antecedent of each postcondition instead. For a body-less
     func this is not just equivalent but identical to what used to be assumed: see
     the `FuncDef { func_body = None }` case in [Checker.check_callable], which turns
     a separate precond/postcond pair into exactly `pre(args) ==> post(args, f(args))`. *)
  (* [mk_chained_and], not [mk_and]: this feeds into a postcondition that gets
     type-checked again below (via [generate_skolem_functions]'s call into
     [Typing.check_symbol]), and the type-checker only accepts `&&` as binary. *)
  let precond_conj = Expr.mk_chained_and preconds in
  let postconds =
    List.map postconds ~f:(fun postcond ->
        Stmt.mk_spec (Expr.mk_impl precond_conj postcond))
  in

  let call_decl =
    Callable.mk_call_decl ~kind:Func ~name:skolem_fn_ident ~loc ~formals:formal_var_decls
      ~returns:[ ret_var_decl ] ~postcond:postconds ~needs_mask:[] ~grants_mask:[] ()
  in

  let* skolem_fn_qual_ident =
    let+ module_qual_ident = Rewriter.current_module_name in

    QualIdent.append module_qual_ident skolem_fn_ident
  in

  let callable = Callable.{ call_decl; call_def = FuncDef { func_body = None } } in

  let symbol = Module.CallDef callable in

  let ret_expr_args_list =
    List.map univ_quants_list ~f:(fun (_, vd) -> Expr.from_var_decl vd)
    @ List.map optn_args ~f:(fun (_, expr) -> expr)
  in

  let ret_expr =
    Expr.mk_app ~typ:var_decl.var_type (Expr.Var skolem_fn_qual_ident) ret_expr_args_list
  in

  let* () =
    Rewriter.Logs.debug (fun printers m ->
        m
          "WitnessComputation.generate_skolem_function: universal_quants: %a \n\
          \ var_decl: %a \n\
          \ postconds: %a \n\
          \ optn_args: %a \n\
          \ output_expr: %a\n\
          \  "
          printers.pr_type_var_decl_list
          (List.map ~f:snd universal_quants.univ_vars)
          printers.pr_type_var_decl var_decl
          (printers.pr_stmt_spec_list "skolemPostConds")
          postconds
          (Util.Print.pr_list_comma (fun ppf (vd, e) ->
               Stdlib.Format.fprintf ppf "%a -> %a" printers.pr_type_var_decl vd
                 printers.pr_expr e))
          optn_args printers.pr_expr ret_expr)
  in

  Rewriter.return (symbol, ret_expr)

let generate_skolem_functions (skolem_fns : skolem_function_def list) =
  let open Rewriter.Syntax in
  let* symbols__ret_exprs =
    Rewriter.List.map skolem_fns ~f:(fun skolem_fn ->
        generate_skolem_function skolem_fn.universal_quants skolem_fn.var_decl
          ~preconds:skolem_fn.preconds ~postconds:skolem_fn.postconds
          ~optn_args:skolem_fn.optn_args ~skolem_id:skolem_fn.skolem_fn_id
          ~loc:skolem_fn.loc)
  in

  let symbols, ret_exprs = List.unzip symbols__ret_exprs in

  let+ _ =
    Rewriter.introduce_typecheck_symbols ~loc:(List.hd_exn skolem_fns).loc
      ~f:Typing.check_symbol symbols
  in

  ret_exprs

let resolve_dependencies (vars : var_decl list) (outer_conds : conditions)
    (candidates : (conditions * expr) list ident_map) =
  let existential_vars =
    Set.of_list (module Ident) (List.map vars ~f:(fun v -> v.Type.var_name))
  in
  let dependencies (conds, witness) =
    List.fold (outer_conds @ conds) ~init:(Expr.local_vars witness) ~f:(fun vars cond ->
        Set.union vars (Expr.local_vars cond))
    |> Set.inter existential_vars
  in
  let initially_resolved =
    Set.filter existential_vars ~f:(fun var -> not (Map.mem candidates var))
  in
  let rec resolve resolved pending witnesses =
    let ready =
      Map.filter_map pending ~f:(fun choices ->
          let choices =
            List.filter choices ~f:(fun choice ->
                Set.is_subset (dependencies choice) ~of_:resolved)
          in
          let unconditional =
            List.filter choices ~f:(fun (conds, _) -> List.is_empty conds)
          in
          let choices = if List.is_empty unconditional then choices else unconditional in
          if List.is_empty choices then None else Some choices)
    in
    let unconditional =
      Map.filter ready ~f:(List.exists ~f:(fun (conds, _) -> List.is_empty conds))
    in
    let ready = if Map.is_empty unconditional then ready else unconditional in
    if Map.is_empty ready then witnesses
    else
      let resolved, pending, witnesses =
        Map.fold ready ~init:(resolved, pending, witnesses)
          ~f:(fun ~key ~data (resolved, pending, witnesses) ->
            (Set.add resolved key, Map.remove pending key, Map.set witnesses ~key ~data))
      in
      resolve resolved pending witnesses
  in
  (* Binding assumptions must have a solution; values and guards cannot depend
     cyclically on the existentials they determine. *)
  resolve initially_resolved candidates (Map.empty (module Ident))

let rec find_witnesses_elim_exists (expr : expr) : (expr * expr list) Rewriter.t =
  elim_a { univ_vars = []; triggers = [] } [] expr

and elim_a (universal_quants : universal_quants) (conds : conditions) (expr : expr) :
    (expr * expr list) Rewriter.t =
  let open Rewriter.Syntax in
  if%bind ProgUtils.is_expr_pure expr then Rewriter.return (expr, [])
  else
    match expr with
    | App (Ite, [ c; e1; e2 ], expr_attr) ->
        let* e1, wtns_specs1 = elim_a universal_quants (c :: conds) e1 in

        let not_c = Expr.mk_not ~loc:(Expr.to_loc c) c in
        let* e2, wtns_specs2 = elim_a universal_quants (not_c :: conds) e2 in

        Rewriter.return
          (Expr.App (Ite, [ c; e1; e2 ], expr_attr), wtns_specs1 @ wtns_specs2)
    | App (Impl, [ c; e2 ], expr_attr) ->
        let+ e2, wtns_specs = elim_a universal_quants (c :: conds) e2 in
        (Expr.App (Impl, [ c; e2 ], expr_attr), wtns_specs)
    | App (And, e_list, expr_attr) ->
        let* e_wtns_specs_list =
          Rewriter.List.map e_list ~f:(fun e -> elim_a universal_quants conds e)
        in

        let e_list, wtns_specs = List.unzip e_wtns_specs_list in

        Rewriter.return (Expr.App (And, e_list, expr_attr), List.concat wtns_specs)
    | Binder (Forall, var_decls, trgs, e, expr_attr) ->
        let universal_quants =
          let new_quants =
            List.map var_decls ~f:(fun var_decl -> (var_decl.var_name, var_decl))
          in
          {
            univ_vars = universal_quants.univ_vars @ new_quants;
            triggers =
              (match universal_quants.triggers with
              | [] -> trgs
              | _ ->
                  List.concat_map universal_quants.triggers ~f:(fun trigs ->
                      List.map trgs ~f:(fun trg -> trigs @ trg)));
          }
        in

        let* e, wtns_specs = elim_a universal_quants conds e in

        Rewriter.return (Expr.Binder (Forall, var_decls, trgs, e, expr_attr), wtns_specs)
    | _ -> elim_a1 universal_quants conds expr

and elim_a1 (univ_vars : universal_quants) (univ_conds : conditions) (expr : expr) :
    (expr * expr list) Rewriter.t =
  let open Rewriter.Syntax in
  (* Flattens multiple existentials *)
  let normalize_expr expr =
    let rec helper_fn expr =
      match expr with
      | Expr.Binder (Exists, vds, bdrs, e, expr_attr) ->
          let vd1, bdrs1, e1 = helper_fn e in
          (vds @ vd1, bdrs @ bdrs1, e1)
      | Expr.App (And, exprs, expr_attr) ->
          let vds_bdrs_exprs = List.map exprs ~f:(fun e -> helper_fn e) in
          let vds, bdrs, exprs = List.unzip3 vds_bdrs_exprs in
          (List.concat vds, List.concat bdrs, Expr.mk_and ~loc:expr_attr.expr_loc exprs)
      | Expr.App (Impl, [ c; e2 ], expr_attr) ->
          let vds, bdrs, e2 = helper_fn e2 in
          (vds, bdrs, Expr.mk_impl ~loc:expr_attr.expr_loc c e2)
      | Expr.App (Ite, [ c; e1; e2 ], expr_attr) ->
          let vds1, bdrs1, e1 = helper_fn e1 in
          let vds2, bdrs2, e2 = helper_fn e2 in
          (vds1 @ vds2, bdrs1 @ bdrs2, Expr.mk_ite ~loc:expr_attr.expr_loc c e1 e2)
      | _ -> ([], [], expr)
    in

    match expr with
    | Expr.Binder (Exists, _, _, _, expr_attr) ->
        let vds, bdrs, e = helper_fn expr in
        Expr.Binder (Exists, vds, bdrs, e, expr_attr)
    | _ -> expr
  in

  let* () =
    Rewriter.Logs.debug (fun printers m ->
        m "WitnessComputation.elim_a1: Pre expr = %a" printers.pr_expr expr)
  in

  let expr = normalize_expr expr in

  match expr with
  | Binder (Exists, var_decls, trgs, e, expr_attr) ->
      let* () =
        Rewriter.Logs.debug (fun printers m ->
            m "WitnessComputation.elim_a1: expr = %a" printers.pr_expr expr)
      in

      let loc = expr_attr.expr_loc in
      let var_decls_skolem_idents =
        List.map var_decls ~f:(fun vd -> (vd, ident_to_skolem_fn_ident ~loc vd.var_name))
      in

      let compute_raw ?(fraction_fallback = false) (vars : var_decl list) =
        let init_map =
          List.fold vars
            ~init:(Map.empty (module Ident))
            ~f:(fun map var_decl -> Map.add_exn map ~key:var_decl.var_name ~data:[])
        in

        elim_a0 ~fraction_fallback univ_vars vars (univ_conds, []) e init_map
      in

      (* Sanitizing witnesses:
       * a. getting rid of expr option; and
       * b. filtering empty lists [] from map *)
      let sanitize (raw : (conditions * expr option) list ident_map) :
          (conditions * expr) list ident_map =
        let witnesses : (conditions * expr) list ident_map =
          Map.map raw ~f:(fun cnd_expr_optn_list ->
              List.filter_map cnd_expr_optn_list ~f:(fun (cnd, expr_optn) ->
                  match expr_optn with None -> None | Some e -> Some (cnd, e)))
        in

        let witnesses : (conditions * expr) list ident_map =
          Map.filter witnesses ~f:(fun cnd_expr_list ->
              not @@ List.is_empty cnd_expr_list)
        in

        witnesses
      in

      let* (raw_witnesses : (conditions * expr option) list ident_map) =
        compute_raw var_decls
      in

      let witnesses =
        resolve_dependencies var_decls univ_conds (sanitize raw_witnesses)
      in

      (* An `own` fraction need not equal the available permission. Use that
         permission as a fallback where primary candidates leave it undetermined;
         see [core_witness_comp]'s `Frac` case. *)
      let* witnesses =
        let unsolved =
          List.filter var_decls ~f:(fun var_decl ->
              match Map.find witnesses var_decl.var_name with
              | None -> true
              | Some choices ->
                  List.for_all choices ~f:(fun (conds, _) -> not (List.is_empty conds)))
        in
        if List.is_empty unsolved then Rewriter.return witnesses
        else
          let+ raw_fallback = compute_raw ~fraction_fallback:true unsolved in
          Map.fold (sanitize raw_fallback) ~init:witnesses ~f:(fun ~key ~data acc ->
              Map.update acc key ~f:(function
                | None -> data
                | Some choices ->
                    (* Keep the fallback only where no primary witness applies. *)
                    let uncovered =
                      List.map choices ~f:(fun (conds, _) ->
                          Expr.mk_not ~loc (Expr.mk_chained_and ~loc conds))
                    in
                    choices
                    @ List.map data ~f:(fun (conds, witness) ->
                        (uncovered @ conds, witness))))
      in

      let witnesses = resolve_dependencies var_decls univ_conds witnesses in

      let existential_vars =
        Set.of_list (module Ident) (List.map var_decls ~f:(fun vd -> vd.var_name))
      in
      let bound_vars =
        Set.union existential_vars
          (Set.of_list (module Ident) (List.map univ_vars.univ_vars ~f:fst))
      in
      let outer_locals =
        List.fold univ_conds
          ~init:(Set.empty (module Ident))
          ~f:(fun vars cond -> Set.union vars (Expr.local_vars cond))
      in
      let witness_locals =
        Map.map witnesses ~f:(fun choices ->
            List.fold choices ~init:outer_locals ~f:(fun vars (conds, witness) ->
                List.fold (witness :: conds) ~init:vars ~f:(fun vars expr ->
                    Set.union vars (Expr.local_vars expr))))
      in
      (* A substituted witness brings its arguments into another witness's guard. *)
      let rec close_environments environments =
        let expanded =
          Map.map environments ~f:(fun vars ->
              Set.fold vars ~init:vars ~f:(fun vars ident ->
                  match Map.find environments ident with
                  | None -> vars
                  | Some dependencies -> Set.union vars dependencies))
        in
        if Map.equal Set.equal environments expanded then environments
        else close_environments expanded
      in
      let environments =
        Map.map (close_environments witness_locals) ~f:(fun vars ->
            Set.diff vars bound_vars)
      in
      let all_env_vars =
        Map.fold environments
          ~init:(Set.empty (module Ident))
          ~f:(fun ~key:_ ~data vars -> Set.union vars data)
      in
      let* env_decls =
        Rewriter.List.map (Set.to_list all_env_vars) ~f:(fun ident ->
            let+ symbol = Rewriter.find_and_reify (QualIdent.from_ident ident) in
            match symbol with
            | VarDef v -> (ident, v.var_decl)
            | _ ->
                Error.internal_error (Ident.to_loc ident)
                  "expected a variable declaration")
      in
      let env_decls = Map.of_alist_exn (module Ident) env_decls in
      let witness_environments =
        Map.map environments ~f:(fun vars ->
            List.map (Set.to_list vars) ~f:(fun ident ->
                let vd = Map.find_exn env_decls ident in
                (vd, Expr.from_var_decl vd)))
      in
      let environment ident =
        Map.find witness_environments ident |> Option.value ~default:[]
      in

      let witness_args_conds_exprs_map =
        Map.mapi witnesses ~f:(fun ~key:iden ~data:witness_list ->
            let witness_arg_exprs =
              List.map witness_list ~f:(fun (conds, witness) ->
                  let optn_arg =
                    {
                      Type.var_name = Ident.fresh loc ("witness_" ^ Ident.to_string iden);
                      var_loc = loc;
                      var_type = Expr.to_type witness |> Type.set_ghost false;
                      var_const = true;
                      var_ghost = false;
                      var_implicit = false;
                    }
                  in

                  (optn_arg, conds, witness))
            in

            witness_arg_exprs)
      in

      let skolem_vars_alpha_renaming_map =
        List.fold var_decls_skolem_idents
          ~init:(Map.empty (module QualIdent))
          ~f:(fun map (vd, skolem_id) ->
            let skolemized_expr =
              let univ_args =
                List.map univ_vars.univ_vars ~f:(fun (_, vd) -> Expr.from_var_decl vd)
              in
              let optn_args =
                begin match Map.find witness_args_conds_exprs_map vd.var_name with
                | None -> []
                | Some arg_conds_expr_list ->
                    List.map arg_conds_expr_list ~f:(fun (arg, cond, expr) -> expr)
                    @ List.map (environment vd.var_name) ~f:snd
                end
              in
              Expr.mk_app ~loc ~typ:vd.var_type
                (Expr.Var (QualIdent.from_ident skolem_id))
                (univ_args @ optn_args)
            in

            match
              Map.add ~key:(QualIdent.from_ident vd.var_name) ~data:skolemized_expr map
            with
            | `Ok map -> map
            | `Duplicate ->
                Error.internal_error loc "Duplicate existentially quantified var")
      in

      let skolem_vars_alpha_renaming_map =
        (* Selected candidates are acyclic; expand their arguments before insertion. *)
        let rec expand expr =
          if Set.is_empty (Set.inter existential_vars (Expr.local_vars expr)) then expr
          else expand (Expr.alpha_renaming expr skolem_vars_alpha_renaming_map)
        in
        Map.map skolem_vars_alpha_renaming_map ~f:expand
      in

      let* () =
        Rewriter.Logs.debug (fun printers m ->
            m "WitnessComputation.elim_a1: witness_map: %a"
              (Fmt.Dump.list (fun ppf (i, e) ->
                   Stdlib.Format.fprintf ppf "%a -> %a" Ident.pr i
                     (Fmt.Dump.list (fun ppf (c, e) ->
                          Stdlib.Format.fprintf ppf "%a -> %a"
                            (Util.Print.pr_list_comma printers.pr_expr)
                            c printers.pr_expr e))
                     e))
              (Map.to_alist witnesses))
      in

      let e_local_vars = Expr.local_vars e in

      let* skolem_fn_records =
        Rewriter.List.map var_decls_skolem_idents ~f:(fun (var_decl, skolem_ident) ->
            let* preconds, postconds, optn_args =
              match Map.find witness_args_conds_exprs_map var_decl.var_name with
              | None | Some [] ->
                  (* Only warn if the variable actually occurs somewhere in the
                   exhaled/asserted expression. If it doesn't occur at all -- e.g.
                   it dropped out entirely once other existentials in the same
                   quantifier were instantiated by an explicit `fold`/`unfold`
                   binding -- then leaving it unconstrained is provably inert:
                   there's nothing left for its value to influence. If it does
                   occur (even only in a pure guard the search doesn't look
                   inside), its value can still affect what gets exhaled or what
                   later code can prove, so the warning stays. *)
                  if Set.mem e_local_vars var_decl.var_name then
                    (* Point at the variable's own binder, `var_decl.var_loc`, rather
                     than the whole existential's `expr` -- which can span many
                     lines and puts the caret nowhere near the actual variable. *)
                    Logs.warn (fun m ->
                        m "%s%s"
                          (Loc.to_string var_decl.var_loc)
                          (Printf.sprintf
                             "No witness could be computed for %s -- it will be treated \
                              as an arbitrary unconstrained value, which may cause later \
                              assertions about it to fail."
                             (Ident.name var_decl.var_name)));

                  Rewriter.return ([], [], [])
              | Some witness_arg_exprs ->
                  let postconds =
                    List.map witness_arg_exprs ~f:(fun (optn_arg, conds, e) ->
                        Expr.mk_impl
                          (Expr.mk_chained_and (univ_conds @ conds))
                          (Expr.mk_eq (Expr.from_var_decl var_decl)
                             (Expr.from_var_decl optn_arg)))
                  in

                  let preconds =
                    List.concat
                    @@ List.mapi witness_arg_exprs
                         ~f:(fun index_outer (optn_arg1, conds1, e1) ->
                           List.rev
                             (List.foldi witness_arg_exprs ~init:[]
                                ~f:(fun index_inner accum (optn_arg2, conds2, e2) ->
                                  if index_outer >= index_inner then accum
                                  else
                                    Expr.mk_impl
                                      (Expr.mk_chained_and (univ_conds @ conds1 @ conds2))
                                      (Expr.mk_eq
                                         (Expr.from_var_decl optn_arg1)
                                         (Expr.from_var_decl optn_arg2))
                                    :: accum)))
                  in

                  let witness_optn_args =
                    List.map witness_arg_exprs ~f:(fun (vd, _, e) -> (vd, e))
                  in

                  let optn_args = witness_optn_args @ environment var_decl.var_name in

                  Rewriter.return (preconds, postconds, optn_args)
            in

            let preconds_sanitized, postconds_sanitized =
              let skolem_vars_alpha_renaming_map_local =
                Map.remove skolem_vars_alpha_renaming_map
                  (QualIdent.from_ident var_decl.var_name)
              in

              let preconds_sanitized =
                List.map preconds ~f:(fun expr ->
                    Expr.alpha_renaming expr skolem_vars_alpha_renaming_map_local)
              in

              let postconds_sanitized =
                List.map postconds ~f:(fun expr ->
                    Expr.alpha_renaming expr skolem_vars_alpha_renaming_map_local)
              in

              (preconds_sanitized, postconds_sanitized)
            in

            Rewriter.return
              {
                universal_quants = univ_vars;
                var_decl;
                preconds = preconds_sanitized;
                postconds = postconds_sanitized;
                optn_args;
                skolem_fn_id = skolem_ident;
                loc = var_decl.var_loc;
              })
      in

      let* skolemized_exprs = generate_skolem_functions skolem_fn_records in

      let* temp_skolem_var_decls__wtns_specs_list : (var_decl * expr) list =
        Rewriter.List.map (List.zip_exn var_decls skolemized_exprs)
          ~f:(fun (var_decl, skolem_expr) ->
            let skolem_wtns_var_tp =
              if List.is_empty univ_vars.univ_vars then var_decl.var_type
              else
                Type.mk_map loc
                  (Type.mk_prod loc
                     (List.map univ_vars.univ_vars ~f:(fun (_, vd) -> vd.var_type)))
                  (* ~~~> *)
                  var_decl.var_type
            in

            let temp_skolem_var_decl =
              {
                var_decl with
                var_name =
                  Ident.fresh loc @@ "$skolem_expr_placeholder$$"
                  ^ Ident.to_string var_decl.var_name;
                var_type = skolem_wtns_var_tp;
                var_const = true;
              }
            in

            let skolem_placeholder_var_def =
              Module.VarDef
                {
                  var_decl = temp_skolem_var_decl;
                  var_init = None;
                  var_is_free = MachineFree;
                }
            in

            let+ _ =
              Rewriter.introduce_typecheck_symbol ~loc ~f:Typing.check_symbol
                skolem_placeholder_var_def
            in

            let wtns_constraint_expr =
              match univ_vars.univ_vars with
              | [] ->
                  Expr.mk_eq ~loc (Expr.from_var_decl temp_skolem_var_decl) skolem_expr
              | _ ->
                  Expr.mk_binder ~loc Forall
                    (List.map univ_vars.univ_vars ~f:(fun (_, vd) -> vd)
                    (* TODO: ^^^ Check if SMTLIB requires univ_vars need to be renamed when used in quantifiers. *))
                    (* :: *)
                    (Expr.mk_eq ~loc
                       (* skolem_var[ univ_vars ] *)
                       (Expr.mk_maplookup
                          (Expr.from_var_decl temp_skolem_var_decl)
                          (Expr.mk_tuple
                             (List.map univ_vars.univ_vars ~f:(fun (_, vd) ->
                                  Expr.from_var_decl vd))))
                       (* == *)
                       skolem_expr)
            in

            (temp_skolem_var_decl, wtns_constraint_expr))
      in

      let temp_skolem_var_var_decls, wtns_specs_exprs =
        List.unzip temp_skolem_var_decls__wtns_specs_list
      in

      let renaming_map =
        List.fold2_exn var_decls temp_skolem_var_var_decls
          ~init:(Map.empty (module QualIdent))
          ~f:(fun map var_decl temp_skolem_var_decl ->
            Map.set map
              ~key:(QualIdent.from_ident var_decl.var_name)
              ~data:
                (match univ_vars.univ_vars with
                | [] -> Expr.from_var_decl temp_skolem_var_decl
                | _ ->
                    Expr.mk_maplookup
                      (Expr.from_var_decl temp_skolem_var_decl)
                      (* [ *)
                      (Expr.mk_tuple
                         (List.map univ_vars.univ_vars ~f:(fun (_, vd) ->
                              Expr.from_var_decl vd)))
                    (* ] *)))
      in

      let* () =
        Rewriter.Logs.debug (fun printers m ->
            m "WitnessComputation.elim_a1: renaming_map: %a"
              (Fmt.Dump.list (fun ppf (qi, e) ->
                   Stdlib.Format.fprintf ppf "%a -> %a" QualIdent.pr qi printers.pr_expr e))
              (Map.to_alist renaming_map))
      in

      let renaming_map_sanitized =
        (* Need to sanitize renaming_map if an existentially quantified expression occurs in a computed witness.
          eg: exists a, b :: x.f |-> (a, 1.) && a.f |-> (b, 1.)
          here renaming map would map
          a ~> (x.f)#0
          b ~> (a.f)#0

        This occurence of `a` in `renaming_map[b]` needs alpha-renamed. *)
        Map.map renaming_map ~f:(fun e -> Expr.alpha_renaming e renaming_map)
      in

      let e = Expr.alpha_renaming e renaming_map_sanitized in
      let wtns_specs_exprs =
        List.map wtns_specs_exprs ~f:(fun wtns_expr ->
            Expr.alpha_renaming wtns_expr renaming_map_sanitized)
      in
      let* e, wtns_specs = elim_a univ_vars univ_conds e in

      Rewriter.return (e, wtns_specs_exprs @ wtns_specs)
  | _ ->
      (* No existentials found *)
      Rewriter.return (expr, [])

and elim_a0 ?(fraction_fallback = false) (univ_vars : universal_quants)
    (exist_vars : var_decl list) ((univ_conds, exist_conds) : conditions * conditions)
    (expr : expr) (witness_map : (conditions * expr option) list ident_map) :
    (conditions * expr option) list ident_map Rewriter.t =
  let open Rewriter.Syntax in
  let elim_a0 = elim_a0 ~fraction_fallback in
  match expr with
  | App (And, e_list, _) ->
      let* witness_map =
        Rewriter.List.fold_left e_list ~init:witness_map ~f:(fun map e ->
            elim_a0 univ_vars exist_vars (univ_conds, exist_conds) e map)
      in

      Rewriter.return witness_map
  | App (Impl, [ c; e2 ], _) ->
      let* witness_map =
        elim_a0 univ_vars exist_vars (univ_conds, c :: exist_conds) e2 witness_map
      in

      Rewriter.return witness_map
  | App (Ite, [ c; e1; e2 ], _) ->
      let* witness_map =
        elim_a0 univ_vars exist_vars (univ_conds, c :: exist_conds) e1 witness_map
      in

      let not_c = Expr.mk_not ~loc:(Expr.to_loc c) c in
      let* witness_map =
        elim_a0 univ_vars exist_vars (univ_conds, not_c :: exist_conds) e2 witness_map
      in

      Rewriter.return witness_map
  | App (Eq, [ left; right ], _) ->
      let add_candidates pattern value witness_map =
        let+ candidates = core_witness_comp exist_vars value pattern true in
        Map.fold candidates ~init:witness_map ~f:(fun ~key ~data witnesses ->
            Map.update witnesses key ~f:(fun existing ->
                (exist_conds, Some data) :: Option.value existing ~default:[]))
      in
      let* witness_map = add_candidates left right witness_map in
      add_candidates right left witness_map
  | App (Own, [ loc_expr; field_expr; val_expr ], _) ->
      let field_name =
        try Expr.to_qual_ident field_expr
        with _ -> Error.type_error (Expr.to_loc field_expr) "Expected field identifier."
      in

      let field_elem_type = field_expr |> Expr.to_type |> Type.field_val in

      (* Resolve before deriving the heap's name, as at the three Own sites
         above: a witness computed against a manifest field's own heap would
         be computed against an empty one. *)
      let* field_name = Rewriter.resolve field_name in
      let field_heap_name = field_heap_name field_name in
      let field_heap_type = Type.mk_map (Expr.to_loc expr) Type.ref field_elem_type in

      let concrete_expr =
        Expr.mk_maplookup
          (Expr.mk_var ~typ:field_heap_type (QualIdent.from_ident field_heap_name))
          loc_expr
      in

      let relevant_vars =
        List.filter exist_vars ~f:(fun var_decl ->
            Set.exists (Expr.local_vars val_expr) ~f:(Ident.equal var_decl.var_name))
      in

      (* For an RA whose rep type is a bare primitive (e.g. `MaxNat`'s `rep type T
         = Int`), expand_type_expr has no nominal wrapper to preserve, so
         `Expr.to_type val_expr` comes back as just `Int` by this point -- unlike
         an ADT-backed RA (e.g. `Auth`), whose data type keeps the module
         identity. Look the RA up directly from the field declaration itself as a
         fallback for core_witness_comp to use when the expression's type alone
         isn't enough to identify it. *)
      let* field_ra_hint =
        let* field_symbol = Rewriter.find_and_reify field_name in
        match field_symbol with
        | FieldDef f -> Rewriter.return (Some (ProgUtils.field_get_ra_qual_iden f))
        | _ -> Rewriter.return None
      in

      let* witnesses =
        core_witness_comp ~ra_hint:field_ra_hint ~fraction_fallback relevant_vars
          concrete_expr val_expr false
      in

      let* () =
        Rewriter.Logs.debug (fun printers m ->
            m "WitnessComputation.elim_a0: witnesses: %a"
              (Fmt.Dump.list (fun ppf (i, e) ->
                   Stdlib.Format.fprintf ppf "%a -> %a" Ident.pr i printers.pr_expr e))
              (Map.to_alist witnesses))
      in

      let witness_map =
        List.fold relevant_vars ~init:witness_map ~f:(fun witness_map var_decl ->
            let existing_val =
              match Map.find witness_map var_decl.var_name with None -> [] | Some v -> v
            in

            let new_val =
              (exist_conds, Map.find witnesses var_decl.var_name) :: existing_val
            in

            Map.set witness_map ~key:var_decl.var_name ~data:new_val)
      in

      Rewriter.return witness_map
  | App (Var qual_ident, args, _) -> (
      let* symbol = Rewriter.find_and_reify qual_ident in

      match symbol with
      | CallDef c
        when Poly.(
               c.call_decl.call_decl_kind = Pred || c.call_decl.call_decl_kind = Invariant)
        ->
          let pred_heap = pred_heap_name qual_ident in
          let* pred_in_types = ProgUtils.pred_in_types qual_ident in
          let* pred_out_types = ProgUtils.pred_out_types qual_ident in

          let* pred_heap_type = ProgUtils.pred_heap_type qual_ident in
          let pred_heap_expr =
            Expr.mk_var (QualIdent.from_ident pred_heap) ~typ:pred_heap_type
          in

          let* pred_val_destr =
            ProgUtils.pred_ra_val_destr_qual_ident (Expr.to_loc expr) qual_ident
          in

          let pred_heap_val =
            Expr.mk_app
              ~typ:(Type.mk_prod (Expr.to_loc expr) pred_out_types)
              (DataDestr pred_val_destr)
              [
                Expr.mk_maplookup pred_heap_expr
                  (Expr.mk_tuple (List.take args (List.length pred_in_types)));
              ]
          in

          let* pred_heap_expanded_type =
            !Rewriter.expand_type_expr_ref (Expr.to_type pred_heap_val)
          in

          let* () =
            Rewriter.Logs.debug (fun printers m ->
                m "WitnessComputation.elim_a0: pred_heap_expanded_type: %a"
                  printers.pr_type pred_heap_expanded_type)
          in

          let pred_heap_val_expanded_typ =
            Expr.set_type pred_heap_val pred_heap_expanded_type
          in

          let concrete_exprs =
            List.mapi
              (List.drop args (List.length pred_in_types))
              ~f:(fun i _ ->
                if List.length pred_out_types = 1 then pred_heap_val_expanded_typ
                else Expr.mk_tuple_lookup pred_heap_val_expanded_typ i)
          in

          let out_args_concrete_exprs =
            List.zip_exn (List.drop args (List.length pred_in_types)) concrete_exprs
          in

          let* witness_map =
            Rewriter.List.fold_left out_args_concrete_exprs ~init:witness_map
              ~f:(fun witness_map (out_arg, concrete_expr) ->
                let* witnesses =
                  core_witness_comp exist_vars concrete_expr out_arg true
                in

                let witness_map =
                  List.fold exist_vars ~init:witness_map ~f:(fun witness_map var_decl ->
                      let existing_val =
                        Option.value (Map.find witness_map var_decl.var_name) ~default:[]
                      in

                      let new_val =
                        (exist_conds, Map.find witnesses var_decl.var_name)
                        :: existing_val
                      in

                      Map.set witness_map ~key:var_decl.var_name ~data:new_val)
                in

                Rewriter.return witness_map)
          in

          let* () =
            Rewriter.Logs.debug (fun printers m ->
                m "WitnessComputation.elim_a0: witness_map: %a"
                  (Fmt.Dump.list (fun ppf (i, e) ->
                       Stdlib.Format.fprintf ppf "%a -> %a" Ident.pr i
                         (Fmt.Dump.list (fun ppf (c, e) ->
                              Stdlib.Format.fprintf ppf "%a -> %a"
                                (Util.Print.pr_list_comma printers.pr_expr)
                                c
                                (Fmt.Dump.option printers.pr_expr)
                                e))
                         e))
                  (Map.to_alist witness_map))
          in

          Rewriter.return witness_map
      | _ -> Rewriter.return witness_map)
  | _ -> Rewriter.return witness_map

and core_witness_comp ?(ra_hint : qual_ident option = None) ?(fraction_fallback = false)
    (exists : var_decl list) (concrete_expr : expr) (given_expr : expr) (exact : bool) :
    expr ident_map Rewriter.t =
  let open Rewriter.Syntax in
  let* () =
    Rewriter.Logs.debug (fun printers m ->
        m
          "WitnessComputation.core_witness_comp: exists: %a, concrete_expr: %a, \
           given_expr: %a, exact: %b"
          (Fmt.Dump.list Ident.pr)
          (List.map exists ~f:(fun v -> v.var_name))
          printers.pr_expr concrete_expr printers.pr_expr given_expr exact)
  in

  match exact with
  | false ->
      let ra_name =
        match Expr.to_type given_expr with
        | App (Var ra_name, [], _) -> QualIdent.pop ra_name
        | App (Data (ra_name, _), [], _) -> QualIdent.pop ra_name
        | tp -> (
            match ra_hint with
            | Some ra_name -> ra_name
            | None ->
                Error.type_error (Expr.to_loc given_expr)
                  ("Expected an RA type; found: " ^ Type.to_string tp))
      in

      (* Resolve before the destructor names below are derived from it: the type
         this came from can name the RA through a manifest field's module rather
         than the module the RA was generated in, and the backend keys on the name
         it is given, not on what that name resolves to. *)
      let* ra_name = Rewriter.resolve ra_name in

      let* orig_name, ra_def, _ = Rewriter.find ra_name in

      if QualIdent.(orig_name = Predefs.lib_auth_mod_qual_ident) then
        match given_expr with
        | App (DataConstr constr_ident, exprs, _) | App (Var constr_ident, exprs, _) ->
            (* #TODO: This exception is added to tackle the case of using AuthRA.auth()/AuthRA.full() functions, which are different from the AuthRA.auth_frag() data constructor. As such, this exception is not added in the explicit calculation which should ideally be fixed. *)
            if
              Ident.(
                QualIdent.unqualify constr_ident = Predefs.lib_auth_frag_constr_ident)
              || Ident.(QualIdent.unqualify constr_ident = Predefs.lib_auth_fun_ident)
              || Ident.(
                   QualIdent.unqualify constr_ident = Predefs.lib_auth_full_fun_ident)
            then
              let auth_chunk =
                Expr.mk_app
                  ~typ:(Expr.to_type (List.hd_exn exprs))
                  (Expr.DataDestr
                     (QualIdent.append ra_name Predefs.lib_auth_frag_destr1_ident))
                  [ concrete_expr ]
              in
              core_witness_comp exists auth_chunk (List.hd_exn exprs) true
              (* Error.error_simple "unimplemented" *)
            else Rewriter.return (Map.empty (module Ident))
        | _ -> Error.type_error (Expr.to_loc given_expr) "Expected a data constructor."
      else if QualIdent.(orig_name = Predefs.lib_frac_mod_qual_ident) then
        match given_expr with
        | App (DataConstr constr_ident, exprs, _) -> (
            if
              not
                Ident.(
                  QualIdent.unqualify constr_ident = Predefs.lib_frac_chunk_constr_ident)
            then Rewriter.return (Map.empty (module Ident))
            else
              (* A `Frac` chunk is `frac_chunk(value, fraction)`, and the two
                 components are determined to different degrees by what the heap
                 holds. The *value* is pinned exactly: whatever fraction is held,
                 `frac_proj1` of it is the value. The *fraction* is not -- the
                 assertion being exhaled asks for at most what is held, so any
                 amount up to `frac_proj2` would do, and picking one is a guess.

                 Hence the fraction is only ever solved in [fraction_fallback]
                 mode, which the caller reserves for existentials that nothing
                 else determined (see [elim_a1]). The guess is then the total
                 available: the largest amount that can possibly work, so it
                 succeeds whenever any choice would for a lower-bound constraint
                 such as `q > 0.0`, and it is the only choice for `q == 1.0`. A
                 wrong guess costs a failed proof, never soundness -- the exhale
                 still asserts the permission is there. *)
              match (fraction_fallback, exprs) with
              | false, _ ->
                  let frac_chunk =
                    Expr.mk_app
                      ~typ:(Expr.to_type (List.hd_exn exprs))
                      (Expr.DataDestr
                         (QualIdent.append ra_name Predefs.lib_frac_chunk_destr1_ident))
                      [ concrete_expr ]
                  in
                  core_witness_comp exists frac_chunk (List.hd_exn exprs) true
              | true, [ _; frac_expr ] ->
                  let frac_amount =
                    Expr.mk_app ~typ:(Expr.to_type frac_expr)
                      (Expr.DataDestr
                         (QualIdent.append ra_name Predefs.lib_frac_chunk_destr2_ident))
                      [ concrete_expr ]
                  in
                  core_witness_comp exists frac_amount frac_expr true
              | true, _ -> Rewriter.return (Map.empty (module Ident)))
        | _ -> Error.type_error (Expr.to_loc given_expr) "Expected a data constructor."
      else if QualIdent.(orig_name = Predefs.lib_agree_mod_qual_ident) then
        match given_expr with
        | App (DataConstr constr_ident, exprs, _) ->
            if Ident.(QualIdent.unqualify constr_ident = Predefs.lib_agree_constr_ident)
            then
              let agree_chunk =
                Expr.mk_app
                  ~typ:(Expr.to_type (List.hd_exn exprs))
                  (Expr.DataDestr
                     (QualIdent.append ra_name Predefs.lib_agree_destr1_ident))
                  [ concrete_expr ]
              in
              core_witness_comp exists agree_chunk (List.hd_exn exprs) true
            else Rewriter.return (Map.empty (module Ident))
        | _ -> Error.type_error (Expr.to_loc given_expr) "Expected a data constructor."
      else Rewriter.return (Map.empty (module Ident))
  | true -> (
      match given_expr with
      | App (((Plus | Minus) as operator), [ left; right ], attr)
        when Type.is_num (Expr.to_type concrete_expr) && Type.is_num attr.expr_type ->
          let invert target other operator first second =
            let target_vars = Expr.local_vars target in
            let other_vars = Expr.local_vars other in
            (* Invert only targets that occur on one side of this operation. *)
            let vars =
              List.filter exists ~f:(fun var ->
                  Set.mem target_vars var.var_name
                  && not (Set.mem other_vars var.var_name))
            in
            let typ = Type.join (Expr.to_type first) (Expr.to_type second) in
            if List.is_empty vars || not (Type.subtype_of typ (Expr.to_type target)) then
              Rewriter.return (Map.empty (module Ident))
            else
              let inverse =
                Expr.mk_app ~loc:attr.expr_loc ~typ operator [ first; second ]
              in
              core_witness_comp vars inverse target true
          in
          let* left_witnesses =
            match operator with
            | Plus -> invert left right Minus concrete_expr right
            | _ -> invert left right Plus concrete_expr right
          in
          let* right_witnesses =
            match operator with
            | Plus -> invert right left Minus concrete_expr left
            | _ -> invert right left Minus left concrete_expr
          in
          Rewriter.return
            (Map.merge left_witnesses right_witnesses ~f:(fun ~key:_ -> function
              | `Both (left, _) | `Left left -> Some left
              | `Right right -> Some right))
      | App (Uminus, [ operand ], attr)
        when Type.is_num (Expr.to_type concrete_expr)
             && Type.subtype_of (Expr.to_type concrete_expr) (Expr.to_type operand) ->
          core_witness_comp exists
            (Expr.mk_app ~loc:attr.expr_loc ~typ:(Expr.to_type concrete_expr) Uminus
               [ concrete_expr ])
            operand true
      | App (Var ident, [], _) ->
          if
            List.exists exists ~f:(fun var_decl ->
                QualIdent.(QualIdent.from_ident var_decl.var_name = ident))
          then
            Rewriter.return
              (Map.singleton (module Ident) (QualIdent.unqualify ident) concrete_expr)
          else Rewriter.return (Map.empty (module Ident))
      | App (Tuple, exprs, _) ->
          let indexed_exprs = List.mapi exprs ~f:(fun i expr -> (expr, i)) in

          let* witness_map =
            Rewriter.List.fold_left indexed_exprs
              ~init:(Map.empty (module Ident))
              ~f:(fun witness_map (expr, index) ->
                let* new_witness_map =
                  core_witness_comp exists
                    (if Int.(List.length indexed_exprs = 1) then concrete_expr
                     else Expr.mk_tuple_lookup concrete_expr index)
                    expr true
                in

                let witness_map =
                  Map.merge witness_map new_witness_map ~f:(fun ~key:_ -> function
                    | `Both (w1, w2) -> Some w1
                    | `Left w1 -> Some w1
                    | `Right w2 -> Some w2)
                in

                Rewriter.return witness_map)
          in

          Rewriter.return witness_map
      | App (DataConstr qual_iden, exprs, _) ->
          let* destrs = ProgUtils.get_data_destrs_from_constr qual_iden in

          let* destrs =
            Rewriter.List.map destrs ~f:(fun destr ->
                let+ destr_ret_type =
                  let* destr_symbol = Rewriter.find_and_reify destr in
                  match destr_symbol with
                  | DestrDef destr -> Rewriter.return destr.destr_return_type
                  | _ ->
                      Error.internal_error (Expr.to_loc given_expr)
                        "expected a destructor definition"
                in

                (destr, destr_ret_type))
          in

          let destr_concrete_exprs_and_sub_exprs =
            List.map2_exn destrs exprs ~f:(fun (destr, ret_typ) expr ->
                (Expr.mk_app ~typ:ret_typ (Expr.DataDestr destr) [ concrete_expr ], expr))
          in

          let* witness_map =
            Rewriter.List.fold_left destr_concrete_exprs_and_sub_exprs
              ~init:(Map.empty (module Ident))
              ~f:(fun witness_map (destr_concrete_expr, sub_expr) ->
                let* new_witness_map =
                  core_witness_comp exists destr_concrete_expr sub_expr true
                in

                let witness_map =
                  Map.merge witness_map new_witness_map ~f:(fun ~key:_ -> function
                    | `Both (w1, w2) -> Some w1
                    | `Left w1 -> Some w1
                    | `Right w2 -> Some w2)
                in

                Rewriter.return witness_map)
          in
          Rewriter.return witness_map
      | _ -> Rewriter.return (Map.empty (module Ident)))

let rec rewrite_stmt (stmt : Stmt.t) : Stmt.t Rewriter.t =
  let open Rewriter.Syntax in
  let loc = Stmt.to_loc stmt in
  match stmt.stmt_desc with
  | Basic (Spec (Exhale, spec)) ->
      let exhale_expr = spec.spec_form in
      let* elim_expr, wtns_specs = find_witnesses_elim_exists exhale_expr in

      let* () =
        Rewriter.Logs.debug (fun printers m ->
            m
              "WitnessComputation.rewrite_stmt: \n\
              \ init exhale_expr: %a \n\
              \ elim exhale_expr: %a\n\
              \          "
              printers.pr_expr exhale_expr printers.pr_expr elim_expr)
      in

      let spec = { spec with spec_form = elim_expr } in
      let exhale_stmt = { stmt with stmt_desc = Basic (Spec (Exhale, spec)) } in

      let wtns_specs_stmts =
        List.map wtns_specs ~f:(fun spec_expr ->
            Stmt.mk_assume_expr ~loc spec_expr
              ~cmnt:"Witness binding `assume`, for existentials during exhale.")
      in

      Rewriter.return (Stmt.mk_block_stmt ~loc (wtns_specs_stmts @ [ exhale_stmt ]))
  | Basic (Spec (Assert, spec)) ->
      let assert_expr = spec.spec_form in
      let* elim_expr, wtns_specs = find_witnesses_elim_exists assert_expr in

      let spec = { spec with spec_form = elim_expr } in
      let assert_stmt = { stmt with stmt_desc = Basic (Spec (Assert, spec)) } in

      let wtns_specs_stmts =
        List.map wtns_specs ~f:(fun spec_expr ->
            Stmt.mk_assume_expr ~loc spec_expr
              ~cmnt:"Witness binding `assume`, for existentials during assert.")
      in

      Rewriter.return (Stmt.mk_block_stmt ~loc (wtns_specs_stmts @ [ assert_stmt ]))
  | _ -> Rewriter.Stmt.descend stmt ~f:rewrite_stmt
