(** The rewrites that lower the front end's output to the form the SMT encoding is
    generated from. *)

open Base
open Ast
open Util

let rec rewrite_expand_types (tp_expr : type_expr) : type_expr Rewriter.t =
  !Rewriter.expand_type_expr_ref tp_expr

let rec rewrite_ret_stmts (callable_decl : Callable.call_decl) (stmt : Stmt.t) :
    Stmt.t Rewriter.t =
  let open Rewriter.Syntax in
  match stmt.stmt_desc with
  | Basic (Return ret_expr) ->
      let loc = Stmt.to_loc stmt in

      let* curr_proc_name = Rewriter.current_scope_id in

      Logs.debug (fun m ->
          m "Lowering.rewrite_ret_stmts: curr_proc_name: %a" QualIdent.pr curr_proc_name);

      let ret_expr_list = Expr.unfold_tuple ret_expr in

      let truncated_returns, dropped_returns =
        List.split_n callable_decl.call_decl_returns (List.length ret_expr_list)
      in

      (*let fresh_dropped_returns =
        List.map dropped_formal_args ~f:(fun var_decl ->
            {
              var_decl with
              var_name =
                Ident.fresh stmt.stmt_loc var_decl.var_name.ident_name;
              var_loc = stmt.stmt_loc;
            })
      in*)
      let dropped_returns_exprs = List.map dropped_returns ~f:Expr.from_var_decl in

      let dropped_returns_vars =
        List.map dropped_returns ~f:(fun decl -> QualIdent.from_ident decl.var_name)
      in

      let ret_expr = Expr.mk_tuple (ret_expr_list @ dropped_returns_exprs) in

      (* Need to ensure that call_decl_returns and call_desc.call_lhs line up *)
      let renaming_map =
        List.fold2_exn callable_decl.call_decl_returns
          (ret_expr_list @ dropped_returns_exprs)
          ~init:(Map.empty (module QualIdent))
          ~f:(fun map var_decl arg_expr ->
            Map.add_exn map ~key:(QualIdent.from_ident var_decl.var_name) ~data:arg_expr)
      in

      (*let renaming_map =
        List.fold2_exn callable_decl.call_decl_returns ret_expr_list
          ~init:(Map.empty (module QualIdent))
          ~f:(fun map var_decl expr ->
            Map.add_exn map
              ~key:(QualIdent.from_ident var_decl.var_name)
              ~data:expr)
      in*)
      let postconds_spec = callable_decl.call_decl_postcond in

      let postcond, spec_error =
        if Callable.is_atomic callable_decl then
          let atomic_token_var =
            Expr.mk_var
              ~typ:(Type.atomic_token curr_proc_name)
              (QualIdent.from_ident
                 (ProgUtils.callable_au_token_ident ~loc callable_decl.call_decl_name))
          in

          let concrete_args =
            List.filter callable_decl.call_decl_formals ~f:(fun var_decl ->
                not var_decl.var_implicit)
          in
          let concrete_args_expr = List.map concrete_args ~f:Expr.from_var_decl in

          let error =
            ( Error.Verification Error.Uncommitted,
              loc,
              "The atomic specification may not have been committed before reaching this \
               return point" )
          in
          ( [
              Expr.mk_app ~loc ~typ:Type.perm (Expr.AUPredCommit curr_proc_name)
                [ atomic_token_var; Expr.mk_tuple concrete_args_expr; ret_expr ];
            ],
            [ Stmt.mk_const_spec_error error ] )
        else
          ( List.map postconds_spec ~f:(fun spec ->
                Expr.alpha_renaming spec.spec_form renaming_map),
            let error =
              ( Error.Verification Error.Postcondition,
                loc,
                "A postcondition may not hold at this return point" )
            in
            [ Stmt.mk_const_spec_error error ] )
      in

      let bind_stmt =
        match dropped_returns with
        | [] -> Stmt.mk_skip ~loc
        | _ ->
            Stmt.mk_bind ~loc dropped_returns_vars
              (Stmt.mk_spec ~atomic:false
                 ~cmnt:("bind added for return stmt: " ^ Stmt.to_string stmt)
                 ~spec_error (Expr.mk_and postcond))
      in

      let postconds_exhale_stmts =
        List.map postcond ~f:(fun expr ->
            Stmt.mk_exhale_expr
              ~cmnt:("exhape added for return stmt: " ^ Stmt.to_string stmt)
              ~loc ~spec_error expr)
      in

      let assume_false =
        Stmt.mk_assume_expr ~loc:stmt.stmt_loc (Expr.mk_bool ~loc:stmt.stmt_loc false)
      in

      let new_stmt =
        Stmt.mk_block_stmt ~loc:stmt.stmt_loc
          ((bind_stmt :: postconds_exhale_stmts) @ [ assume_false ])
      in

      Rewriter.return new_stmt
  | _ -> Rewriter.Stmt.descend stmt ~f:(rewrite_ret_stmts callable_decl)

let rec rewrite_new_stmts (stmt : Stmt.t) : Stmt.t Rewriter.t =
  let open Rewriter.Syntax in
  match stmt.stmt_desc with
  | Basic (New new_desc) ->
      let* () =
        Rewriter.Logs.debug (fun printers m ->
            m "Lowering.rewrite_new_stmts: new_desc: %a" printers.pr_stmt stmt)
      in

      let assume_non_null_stmt =
        Stmt.mk_assume_expr ~loc:stmt.stmt_loc ~cmnt:"AssumeNonNull Stmt; from new stmt"
          (Expr.mk_not
             (Expr.mk_eq (Expr.mk_null ()) (Expr.mk_var ~typ:Type.ref new_desc.new_lhs)))
      in
      let* validity_check_optns =
        Rewriter.List.map new_desc.new_args ~f:(fun (fld_qi, e_opt) ->
            match e_opt with
            | None -> Rewriter.return None
            | Some e ->
                let* symbol = Rewriter.find fld_qi in
                let field =
                  match Rewriter.Symbol.orig_symbol symbol with
                  | FieldDef field -> field
                  | _ -> Error.internal_error stmt.stmt_loc "expected a field_def"
                in
                let+ field_type = Rewriter.Symbol.reify_type stmt.stmt_loc symbol in
                let field_symbol = { field with field_type } in

                let field_ra_valid_qi =
                  let field_ra = ProgUtils.field_get_ra_qual_iden field_symbol in
                  ProgUtils.get_ra_valid_fn_qual_ident field_ra
                in
                let assert_stmt =
                  let error =
                    ( Error.Verification Error.Allocation,
                      stmt.stmt_loc,
                      "Could not prove validity of initially-allocated value" )
                  in
                  Stmt.mk_assert_expr ~loc:stmt.stmt_loc
                    ~cmnt:("new() stmt: " ^ Stmt.to_string stmt)
                    ~spec_error:[ Stmt.mk_const_spec_error error ]
                    (Expr.mk_app ~loc:stmt.stmt_loc ~typ:Type.bool
                       (Expr.Var field_ra_valid_qi) [ e ])
                in
                Some assert_stmt)
      in
      let validity_check_stmts = List.filter_map validity_check_optns ~f:(fun f -> f) in
      let havoc_stmt =
        Stmt.mk_havoc ~loc:stmt.stmt_loc
          (* ~cmnt:"RefVar Havoc Stmt; from new stmt" *)
          new_desc.new_lhs
      in

      let* new_inhale_stmts =
        Rewriter.List.map new_desc.new_args ~f:(fun (field_name, expr_optn) ->
            let* field_val =
              match expr_optn with
              | Some expr -> Rewriter.return expr
              | None -> ProgUtils.get_field_utils_id field_name
            in

            let* field_symbol = Rewriter.find field_name in
            let* field_type = Rewriter.Symbol.reify_type stmt.stmt_loc field_symbol in

            let inhale_expr =
              Expr.mk_app ~typ:Type.perm ~loc:stmt.stmt_loc Expr.Own
                [
                  Expr.mk_var ~typ:Type.ref new_desc.new_lhs;
                  Expr.mk_var ~typ:field_type field_name;
                  field_val;
                ]
            in

            let inhale_stmt =
              Stmt.mk_inhale_expr
                ~cmnt:("new stmt: " ^ Stmt.to_string stmt)
                ~loc:stmt.stmt_loc inhale_expr
            in

            Rewriter.return inhale_stmt)
      in

      Rewriter.return
        (Stmt.mk_block_stmt ~loc:stmt.stmt_loc
           (validity_check_stmts
           @ (havoc_stmt :: assume_non_null_stmt :: new_inhale_stmts)))
  | _ -> Rewriter.Stmt.descend stmt ~f:rewrite_new_stmts

type unfolded = {
  pred : string;
  instances : string list;
  inputs : string list;
  mentions : (Ident.t, Ident.comparator_witness) Set.t;
  bound : (Ident.t * Expr.t * Loc.t) list;
}
(** A predicate instance that an unfold opened: the predicate, the instance's spellings,
    as the predicate and arguments, which a copy of the arguments adds to, the arguments,
    the variables these mention, and the variables bound to its existentials, with the
    unfold's location. A fold of the same instance falls back to these values for the
    existentials that witness computation finds no witness for. *)

let instance_name pred args = Printf.sprintf "%s(%s)" pred (String.concat ~sep:", " args)
let is_instance instance u = List.mem u.instances instance ~equal:String.equal

(** [u], also spelled with the components of [x] if [stmt] copies its arguments to [x], as
    the atomicity analysis does when it opens an invariant. *)
let add_copy (stmt : Stmt.t) (u : unfolded) : unfolded =
  match stmt.stmt_desc with
  | Basic (Assign { assign_lhs = [ x ]; assign_rhs; _ }) ->
      let copied = match assign_rhs with App (Tuple, es, _) -> es | e -> [ e ] in
      let n = List.length u.inputs in
      if
        n <= List.length copied
        && List.equal String.equal u.inputs
             (List.map (List.take copied n) ~f:Expr.to_string)
      then
        let copy = Expr.mk_var ~typ:(Expr.to_type assign_rhs) x in
        let components =
          List.init n ~f:(fun i -> Expr.to_string (Expr.mk_tuple_lookup copy i))
        in
        { u with instances = instance_name u.pred components :: u.instances }
      else u
  | _ -> u

(** The existentials of [expr] outside any universal quantifier and negation, with their
    types: those an unfold can bind to variables. *)
let rec top_existentials (expr : Expr.t) : (Ident.t * Type.t) list =
  match expr with
  | Binder (Exists, vds, _, body, _) ->
      List.map vds ~f:(fun vd -> (vd.var_name, vd.var_type)) @ top_existentials body
  | App (And, args, _) -> List.concat_map args ~f:top_existentials
  | App (Ite, [ _; a; b ], _) -> top_existentials a @ top_existentials b
  | App (Impl, [ _; b ], _) -> top_existentials b
  | _ -> []

(** The variables [stmt] assigns, if it is a basic statement. *)
let assigned_vars (stmt : Stmt.t) : Ident.t list =
  let idents = List.map ~f:QualIdent.unqualify in
  match stmt.stmt_desc with
  | Basic (Assign { assign_lhs; _ }) -> idents assign_lhs
  | Basic (Bind { bind_lhs; _ }) -> idents bind_lhs
  | Basic (Havoc { havoc_var; _ }) -> idents [ havoc_var ]
  | Basic (Call { call_lhs; _ }) -> idents call_lhs
  | Basic (New { new_lhs; _ }) -> idents [ new_lhs ]
  | Basic (FieldRead { field_read_lhs; _ }) -> idents [ field_read_lhs ]
  | Basic (AUAction { auaction_kind = OpenAU { lhs; _ } }) ->
      List.concat_map lhs ~f:(fun e -> Set.to_list (Expr.local_vars e))
  | _ -> []

(** Replaces a `fold p(x, y)` stmt with `exhale p(); inhale p.body`, and an unfold
    conversely. *)
let rec rewrite_fold_unfold_stmts (stmt : Stmt.t) : Stmt.t Rewriter.t =
  let open Rewriter.Syntax in
  let+ stmt, _ = track_unfolds [] stmt in
  stmt

(** [stmt] with its folds and unfolds lowered, given the instances [unfolded] open before
    it, and those open after it: through blocks and branches, but not into or out of loops
    and extension statements; an assignment to a variable an instance mentions ends it. *)
and track_unfolds (unfolded : unfolded list) (stmt : Stmt.t) :
    (Stmt.t * unfolded list) Rewriter.t =
  let open Rewriter.Syntax in
  match stmt.stmt_desc with
  | Basic (Use use_desc) -> rewrite_use unfolded stmt use_desc
  | Block block ->
      let+ unfolded, body =
        Rewriter.List.fold_left block.block_body ~init:(unfolded, [])
          ~f:(fun (unfolded, body) s ->
            let+ s, unfolded = track_unfolds unfolded s in
            (unfolded, s :: body))
      in
      ({ stmt with stmt_desc = Block { block with block_body = List.rev body } }, unfolded)
  | Cond cond ->
      let* cond_then, after_then = track_unfolds unfolded cond.cond_then in
      let+ cond_else, after_else = track_unfolds unfolded cond.cond_else in
      (* Instances open after both arms, with the same bindings, or after the else arm
         if the then arm does not continue. *)
      let joined =
        if cond.cond_if_assumes_false then after_else
        else
          List.filter after_then ~f:(fun u ->
              List.exists after_else ~f:(fun v ->
                  List.equal String.equal u.instances v.instances
                  && List.equal
                       (fun (x, e, _) (y, f, _) ->
                         Ident.(x = y)
                         && String.equal (Expr.to_string e) (Expr.to_string f))
                       u.bound v.bound))
      in
      ({ stmt with stmt_desc = Cond { cond with cond_then; cond_else } }, joined)
  | Basic _ ->
      let assigned = assigned_vars stmt in
      Rewriter.return
        ( stmt,
          List.filter_map unfolded ~f:(fun u ->
              if List.exists assigned ~f:(fun x -> Set.mem u.mentions x) then None
              else Some (add_copy stmt u)) )
  | Loop _ | StmtExt _ ->
      let+ stmt =
        Rewriter.Stmt.descend stmt ~f:(fun s ->
            let+ s, _ = track_unfolds [] s in
            s)
      in
      (stmt, [])

(** The lowering of the fold or unfold [stmt] of [use_desc], given the instances
    [unfolded] open before it, and those open after it. *)
and rewrite_use (unfolded : unfolded list) (stmt : Stmt.t) (use_desc : Stmt.use_desc) :
    (Stmt.t * unfolded list) Rewriter.t =
  let open Rewriter.Syntax in
  let loc = stmt.stmt_loc in
  begin
    let* pred_qual_ident, symbol = Rewriter.resolve_and_find use_desc.use_name in
    let* symbol = Rewriter.Symbol.reify symbol in

    let pred_decl, body =
      match symbol with
      | CallDef c ->
          let spec =
            match c.call_def with
            | ProcDef p ->
                Error.internal_error stmt.stmt_loc
                  "expected a func_def inside a fold/unfold stmt"
            | FuncDef { func_body = None } ->
                Error.error stmt.stmt_loc (*(QualIdent.to_loc use_desc.use_name)*)
                  ("Cannot (un)fold abstract predicate "
                  ^ (use_desc.use_name |> QualIdent.unqualify |> Ident.to_string))
                (* TW: this should already be checked during typing *)
            | FuncDef { func_body = Some e } -> e
          in

          (c.call_decl, Expr.set_loc spec (Stmt.to_loc stmt))
      | _ -> Error.internal_error stmt.stmt_loc "expected a call_def"
    in

    begin match (pred_decl.call_decl_kind, pred_decl.call_decl_is_inline) with
    | Pred, true ->
        let error =
          ( Error.Generic,
            loc,
            "Cannot (un)fold inline predicate: "
            ^ Ident.to_string pred_decl.call_decl_name )
        in
        Logs.warn (fun m -> m "%s" (Error.to_string error));
        Rewriter.return (Stmt.mk_skip ~loc, unfolded)
    | _ ->
        let truncated_formal_args, dropped_formal_args =
          List.split_n
            (pred_decl.call_decl_formals @ pred_decl.call_decl_returns)
            (List.length use_desc.use_args)
        in

        let new_dropped_args =
          List.map dropped_formal_args ~f:(fun var_decl ->
              {
                var_decl with
                var_name = Ident.fresh stmt.stmt_loc var_decl.var_name.ident_name;
                var_loc = stmt.stmt_loc;
              })
        in

        let new_dropped_args_exprs = List.map new_dropped_args ~f:Expr.from_var_decl in
        let* _ =
          Rewriter.List.map new_dropped_args ~f:(fun var ->
              Rewriter.introduce_symbol
                (Module.VarDef { var_decl = var; var_init = None; var_is_free = NotFree }))
        in

        let new_renaming_map =
          List.fold2_exn
            (truncated_formal_args @ dropped_formal_args)
            (use_desc.use_args @ new_dropped_args_exprs)
            ~init:(Map.empty (module QualIdent))
            ~f:(fun map var_decl arg_expr ->
              Map.add_exn map ~key:(QualIdent.from_ident var_decl.var_name) ~data:arg_expr)
        in

        let new_body =
          Expr.alpha_renaming body new_renaming_map |> Fn.flip Expr.set_loc loc
        in

        let existential_var_idens_set = Expr.existential_vars new_body in

        (* Resolve a name written in a `[x := e]` clause against the bound variables of
         the predicate's body. Matching is by *base* name, since the user writes the
         name as it appears in the source while the body carries disambiguated ones
         (`vs^4`) -- but one base name can match several once an `auto` predicate has
         been inlined into the body, bringing its own bound variables along (see
         [rewrite_inline_preds_expr]). Those are invisible in the source the user is
         looking at, so the clash is not their mistake, but neither is it something to
         resolve by guessing: picking one arbitrarily substituted a variable of one type
         where another was meant, and the result surfaced as malformed SMT and an
         internal error rather than as any kind of diagnosis. *)
        let resolve_existential (written : Ident.t) : Ident.t option =
          match
            Set.to_list existential_var_idens_set
            |> List.filter ~f:(fun ex ->
                String.(ex.Ident.ident_name = written.ident_name))
          with
          | [] -> None
          | [ v ] -> Some v
          | several ->
              let types = Expr.existential_vars_type new_body in
              let described =
                List.map several ~f:(fun v ->
                    match Map.find types v with
                    | Some tp -> Printf.sprintf !"one of type %{Type}" tp
                    | None -> "one")
                |> String.concat ~sep:", "
              in
              Error.type_error stmt.stmt_loc
                (Printf.sprintf
                   !"%{Ident} does not name a single bound variable of %{QualIdent}: \
                     there are %d of that name in its body (%s), so this does not say \
                     which one is meant. Either the body binds the name twice, or an \
                     `auto` predicate inlined into it brings a bound variable of the \
                     same name along -- which is not visible in the source. Rename so \
                     that the name is unique"
                   written use_desc.use_name (List.length several) described)
        in

        let user_exist_binds, user_exist_witnesses =
          match use_desc.use_kind with
          | Fold -> ([], use_desc.use_witnesses_or_binds)
          | Unfold -> (use_desc.use_witnesses_or_binds, [])
        in

        let* user_exist_binds_renam_map =
          Rewriter.List.fold_left user_exist_binds
            ~init:(Map.empty (module QualIdent))
            ~f:(fun mp (bd_iden, exis_expr) ->
              let exis_iden = Expr.to_qual_ident exis_expr |> QualIdent.unqualify in
              match resolve_existential exis_iden with
              | None -> Rewriter.return mp
              | Some v ->
                  Logs.debug (fun m ->
                      m
                        "Lowering.rewrite_fold_unfold_stmts : \n\
                        \                bd_iden = %a\n\
                        \                exis_iden = %a\n\
                        \              "
                        Ident.pr bd_iden Ident.pr exis_iden);

                  let+ bd_var_decl =
                    let* symbol = Rewriter.find (QualIdent.from_ident bd_iden) in
                    Rewriter.Symbol.reify_var_decl symbol
                  in

                  let bd_var_expr = Expr.from_var_decl bd_var_decl in
                  Map.set mp ~key:(QualIdent.from_ident v) ~data:bd_var_expr)
        in

        (* An unfold binds the existentials the user does not bind to fresh variables,
             for a later fold of the same instance to fall back to. *)
        let* fallback_vars =
          match use_desc.use_kind with
          | Fold -> Rewriter.return []
          | Unfold ->
              Rewriter.List.map (top_existentials new_body) ~f:(fun (x, typ) ->
                  let var_decl =
                    {
                      Type.var_name =
                        Ident.fresh loc (WitnessComputation.fallback_prefix ^ x.ident_name);
                      var_loc = loc;
                      var_type = Type.set_ghost true typ;
                      var_const = false;
                      var_ghost = true;
                      var_implicit = false;
                    }
                  in
                  let+ _ =
                    Rewriter.introduce_symbol
                      (Module.VarDef { var_decl; var_init = None; var_is_free = NotFree })
                  in
                  (x, var_decl))
        in
        (* The existentials the user binds keep their fallback variables equal to the
           user's; the others are bound to them. *)
        let auto_binds, user_bound =
          List.partition_map fallback_vars ~f:(fun (x, vd) ->
              match Map.find user_exist_binds_renam_map (QualIdent.from_ident x) with
              | None -> First (x, vd)
              | Some user -> Second (vd, user))
        in
        let user_exist_binds_renam_map =
          List.fold auto_binds ~init:user_exist_binds_renam_map ~f:(fun mp (x, vd) ->
              Map.set mp ~key:(QualIdent.from_ident x) ~data:(Expr.from_var_decl vd))
        in

        (* The instance: the predicate and the arguments of its inputs. *)
        let inputs =
          List.take use_desc.use_args (List.length pred_decl.call_decl_formals)
        in
        let instance =
          instance_name
            (QualIdent.to_string pred_qual_ident)
            (List.map inputs ~f:Expr.to_string)
        in
        let others = List.filter unfolded ~f:(fun u -> not (is_instance instance u)) in

        let user_witness_renam_map =
          List.fold user_exist_witnesses
            ~init:(Map.empty (module QualIdent))
            ~f:(fun mp (iden, wtns_expr) ->
              match resolve_existential iden with
              | None -> mp
              | Some v -> Map.set mp ~key:(QualIdent.from_ident v) ~data:wtns_expr)
        in

        (* The values the existentials had at the unfold of the instance, as witnesses of
           a fold for those the user gives none for. *)
        let fallback_renam_map =
          match use_desc.use_kind with
          | Unfold -> user_witness_renam_map
          | Fold -> (
              match List.find unfolded ~f:(is_instance instance) with
              | None -> user_witness_renam_map
              | Some u ->
                  List.fold u.bound ~init:user_witness_renam_map
                    ~f:(fun map (x, value, _) ->
                      let x = QualIdent.from_ident x in
                      if Map.mem map x then map else Map.set map ~key:x ~data:value))
        in

        (* The out-parameters are bound without the fallbacks, which may not fit any more. *)
        let body_fold_expr, body_bind_expr, body_unfold_expr =
          let exhale_expr = Expr.supply_witnesses fallback_renam_map new_body in
          let bind_expr = Expr.supply_witnesses user_witness_renam_map new_body in
          let inhale_expr = Expr.supply_witnesses user_exist_binds_renam_map new_body in

          (exhale_expr, bind_expr, inhale_expr)
        in

        (* The instance as written: its arguments are the caller's own expressions, to
             which the predicate's parameters do not apply. *)
        let pred_expr =
          Expr.mk_app ~loc ~typ:Type.bool (Expr.Var use_desc.use_name)
            (use_desc.use_args @ new_dropped_args_exprs)
        in

        let new_stmt =
          match use_desc.use_kind with
          | Fold -> (
              let spec_error =
                match use_desc.use_spec_error with
                | _ :: _ as spec_error -> spec_error
                | [] ->
                    let error =
                      ( Error.Verification Error.Fold,
                        stmt.stmt_loc,
                        "Failed to fold predicate. The body of the predicate may not \
                         hold at this point" )
                    in
                    [ Stmt.mk_const_spec_error error ]
              in
              let spec_form = Stmt.mk_spec ~spec_error body_bind_expr in
              let bind_stmt =
                Stmt.mk_bind ~loc:stmt.stmt_loc
                  (List.map new_dropped_args ~f:(fun var_decl ->
                       QualIdent.from_ident var_decl.var_name))
                  spec_form
              in

              let inhale_stmt =
                Stmt.mk_inhale_expr ~loc
                  ~cmnt:("fold : " ^ Expr.to_string pred_expr)
                  pred_expr
              in

              let exhale_stmt =
                Stmt.mk_exhale_expr ~loc
                  ~cmnt:("fold : " ^ Expr.to_string pred_expr)
                  ~spec_error ~spec_source:(pred_qual_ident, 0) body_fold_expr
              in
              match new_dropped_args with
              | [] -> Stmt.mk_block_stmt ~loc [ exhale_stmt; inhale_stmt ]
              | _ -> Stmt.mk_block_stmt ~loc [ bind_stmt; exhale_stmt; inhale_stmt ])
          | Unfold -> (
              let inhale_stmt =
                let usr_binds_havocs =
                  List.map use_desc.use_witnesses_or_binds ~f:(fun (i, e) ->
                      Stmt.mk_havoc ~loc (QualIdent.from_ident i))
                  @ List.map fallback_vars ~f:(fun (_, vd) ->
                      Stmt.mk_havoc ~loc (QualIdent.from_ident vd.var_name))
                in

                let pred_body_inhale_stmt =
                  Stmt.mk_inhale_expr ~loc
                    ~cmnt:("unfold : " ^ Expr.to_string pred_expr)
                    ~spec_source:(pred_qual_ident, 0) body_unfold_expr
                in

                let fallback_assumes =
                  List.map user_bound ~f:(fun (vd, user) ->
                      Stmt.mk_assume_expr ~loc (Expr.mk_eq (Expr.from_var_decl vd) user))
                in
                Stmt.mk_block_stmt ~loc
                  ((usr_binds_havocs @ [ pred_body_inhale_stmt ]) @ fallback_assumes)
              in

              let spec_error =
                let error =
                  ( Error.Verification Error.Unfold,
                    stmt.stmt_loc,
                    "Failed to unfold predicate. The predicate may not hold at this point"
                  )
                in
                [ Stmt.mk_const_spec_error error ]
              in

              let bind_stmt =
                Stmt.mk_bind ~loc:stmt.stmt_loc
                  (List.map new_dropped_args ~f:(fun var_decl ->
                       QualIdent.from_ident var_decl.var_name))
                  (Stmt.mk_spec pred_expr ~spec_error)
              in

              let exhale_stmt =
                Stmt.mk_exhale_expr ~loc
                  ~cmnt:("unfold : " ^ Expr.to_string pred_expr)
                  ~spec_error pred_expr
              in
              match new_dropped_args with
              | [] -> Stmt.mk_block_stmt ~loc [ exhale_stmt; inhale_stmt ]
              | _ -> Stmt.mk_block_stmt ~loc [ bind_stmt; exhale_stmt; inhale_stmt ])
        in
        (* A fold closes the instance, and an unfold opens it, with its bindings. *)
        let after =
          match use_desc.use_kind with
          | Fold -> others
          | Unfold ->
              (* The fallback variables, also of the existentials the user binds, whose
                 names may not be in scope at the fold. *)
              let bound =
                List.map fallback_vars ~f:(fun (x, vd) -> (x, Expr.from_var_decl vd, loc))
              in
              let mentions =
                List.fold
                  (inputs @ List.map bound ~f:(fun (_, e, _) -> e))
                  ~init:(Set.empty (module Ident))
                  ~f:(fun vars e -> Set.union vars (Expr.local_vars e))
              in
              {
                pred = QualIdent.to_string pred_qual_ident;
                instances = [ instance ];
                inputs = List.map inputs ~f:Expr.to_string;
                mentions;
                bound;
              }
              :: others
        in
        Rewriter.return (new_stmt, after)
    end
  end

let rec rewrite_call_stmts (stmt : Stmt.t) : Stmt.t Rewriter.t =
  let open Rewriter.Syntax in
  match stmt.stmt_desc with
  | Basic (Call call_desc) -> (
      let* callee_qual_ident, symbol = Rewriter.resolve_and_find call_desc.call_name in
      let call_def =
        match Rewriter.Symbol.orig_symbol symbol with
        | CallDef c -> c.call_def
        | _ -> Error.internal_error stmt.stmt_loc "expected a call_def"
      in
      let* call_decl = Rewriter.Symbol.reify_callable_decl symbol in
      let call_decl =
        if call_desc.call_is_spawn then
          { call_decl with call_decl_postcond = []; call_decl_returns = [] }
        else call_decl
      in

      let _, dropped_returns =
        List.split_n call_decl.call_decl_returns (List.length call_desc.call_lhs)
      in

      let* fresh_dropped_returns =
        Rewriter.List.map dropped_returns ~f:(fun var_decl ->
            let new_var_decl =
              {
                var_decl with
                var_name = Ident.fresh stmt.stmt_loc var_decl.var_name.ident_name;
                var_loc = stmt.stmt_loc;
              }
            in
            let+ _ =
              Rewriter.introduce_symbol
                (Module.VarDef
                   { var_decl = new_var_decl; var_init = None; var_is_free = NotFree })
            in
            new_var_decl)
      in

      let* lhs_list =
        Rewriter.List.map call_desc.call_lhs ~f:(fun name ->
            let* symbol = Rewriter.find name in
            Rewriter.Symbol.reify_var_decl symbol)
      in
      let lhs_list = lhs_list @ fresh_dropped_returns in

      let* new_lhs_list =
        Rewriter.List.map lhs_list ~f:(fun lhs ->
            let new_var_name =
              Ident.fresh stmt.stmt_loc (lhs.var_name.ident_name ^ "$ret")
            in
            let new_var_decl = { lhs with var_name = new_var_name } in
            let* _ =
              Rewriter.introduce_symbol
                (Module.VarDef
                   { var_decl = new_var_decl; var_init = None; var_is_free = NotFree })
            in

            Rewriter.return (Expr.from_var_decl new_var_decl))
      in

      let* new_renaming_map, new_dropped_args =
        let truncated_formal_args, dropped_formal_args =
          List.split_n call_decl.call_decl_formals (List.length call_desc.call_args)
        in

        let fresh_dropped_args =
          List.map dropped_formal_args ~f:(fun var_decl ->
              {
                var_decl with
                var_name = Ident.fresh stmt.stmt_loc var_decl.var_name.ident_name;
                var_loc = stmt.stmt_loc;
              })
        in

        let fresh_dropped_args_exprs =
          List.map fresh_dropped_args ~f:Expr.from_var_decl
        in

        (* Need to ensure that call_decl_returns and call_desc.call_lhs line up *)
        let renaming_map =
          List.fold2_exn
            (truncated_formal_args @ dropped_formal_args @ call_decl.call_decl_returns)
            (call_desc.call_args @ fresh_dropped_args_exprs @ new_lhs_list)
            ~init:(Map.empty (module QualIdent))
            ~f:(fun map var_decl arg_expr ->
              Map.add_exn map ~key:(QualIdent.from_ident var_decl.var_name) ~data:arg_expr)
        in

        Rewriter.return (renaming_map, fresh_dropped_args)
      in

      let* () =
        Rewriter.Logs.debug (fun printers m ->
            m "Lowering.rewrite_call_stmts: new_renaming_map: %a"
              (Util.Print.pr_map ~key:QualIdent.pr ~value:printers.pr_expr)
              new_renaming_map)
      in

      match call_def with
      | ProcDef _ ->
          let* _ =
            Rewriter.List.map new_dropped_args ~f:(fun var ->
                Rewriter.introduce_symbol
                  (Module.VarDef
                     { var_decl = var; var_init = None; var_is_free = NotFree }))
          in

          (* let build_exhale_spec (spec: Stmt.spec) =
               (* renames args from old to new. Also, existentially quantifies over relevant implicit variables. *)
               let spec_form = Expr.alpha_renaming spec.spec_form renaming_map in

               let used_implicit_vars = List.filter (List.zip_exn quant_dropped_args new_dropped_args) ~f:(
                 fun (var_decl1, var_decl2) ->
                   Set.mem (Expr.local_vars spec_form) var_decl1.var_name
               ) in

               let eqs = List.map used_implicit_vars ~f:(fun (v_d1, v_d2) -> Expr.mk_eq (Expr.from_var_decl v_d1) (Expr.from_var_decl v_d2)) in

               let used_quant_vars, _ = List.unzip used_implicit_vars in

               let spec_form = Expr.mk_binder ~loc:stmt.stmt_loc ~typ:Type.bool Exists used_quant_vars (Expr.mk_and (spec_form :: eqs)) in

               { spec with spec_form }
             in

             let build_inhale_spec (spec: Stmt.spec) =
               let spec_form = Expr.alpha_renaming spec.spec_form renaming_map2 in

               { spec with spec_form }
             in *)
          let spec_error =
            match
              List.map call_decl.call_decl_precond ~f:(fun spec -> spec.spec_error)
            with
            | (_ :: _ as err) :: _ -> err
            | _ -> []
          in
          let spec_form =
            Stmt.mk_spec
              ~cmnt:("Bind stmt for Call: " ^ Stmt.to_string stmt)
              ~spec_error
              (Expr.mk_and
                 (List.map call_decl.call_decl_precond ~f:(fun spec ->
                      Expr.alpha_renaming spec.spec_form new_renaming_map)))
          in

          let bind_stmt =
            (* TODO: can we preserve the error messages for the individual preconditions here? *)
            Stmt.mk_bind ~loc:stmt.stmt_loc
              (List.map new_dropped_args ~f:(fun var_decl ->
                   QualIdent.from_ident var_decl.var_name))
              spec_form
          in

          (* An abort check has already given up both preconditions using the
             same selected frame. Other calls still give up their preconditions here. *)
          let exhale_stmts =
            List.filter_mapi call_decl.call_decl_precond ~f:(fun i spec ->
                Option.some_if (not call_desc.call_precond_given)
                @@
                (* Logs.debug (fun m -> m "Lowering.rewrite_call_stmts: Exhale_stmt=%a; Exhale_stmt_error_len = %i; Exhale_stmt_error=%s" Expr.pr spec.spec_form (List.length spec_error) (Error.to_string ((List.hd_exn spec_error) (QualIdent.from_ident call_decl.call_decl_name) stmt.stmt_loc)) ); *)
                (* The name of a named loop invariant, which is the precondition of the
                   loop's procedure, names its checks on entry and maintenance. *)
                Stmt.mk_exhale_expr ~loc:stmt.stmt_loc ?name:spec.spec_name
                  ~cmnt:("Exhale stmt for Call: " ^ Stmt.to_string stmt)
                  ~spec_error:spec.spec_error ~spec_source:(callee_qual_ident, i)
                  (Expr.alpha_renaming spec.spec_form new_renaming_map))
          in

          (* One inhale per postcond clause (rather than a single inhale of their
             conjunction) so each can carry its own [spec_source] -- `assume (p && q)`
             and `assume p; assume q` are equivalent, so this is not an observable
             behavior change. *)
          let num_precond = List.length call_decl.call_decl_precond in
          let inhale_stmts =
            List.mapi call_decl.call_decl_postcond ~f:(fun j spec ->
                Stmt.mk_inhale_expr ~loc:stmt.stmt_loc
                  ~cmnt:("Inhale stmt for Call: " ^ Stmt.to_string stmt)
                  ~spec_source:(callee_qual_ident, num_precond + j)
                  (Expr.alpha_renaming spec.spec_form new_renaming_map))
          in

          let reassign_lhs_stmt =
            Stmt.mk_assign ~loc:stmt.stmt_loc ~is_init:call_desc.call_is_init
              (List.map lhs_list ~f:(fun decl -> QualIdent.from_ident decl.var_name))
              (Expr.mk_tuple new_lhs_list)
          in

          (* TODO: Need to havoc ret vars before inhaling postconditions *)
          let new_stmt =
            Stmt.mk_block_stmt ~loc:stmt.stmt_loc
              (* (if (List.is_empty call_decl.call_decl_precond ) then *)
              (* [inhale_stmt] *)
              (* else *)
              (match (new_dropped_args, lhs_list) with
              | [], [] -> exhale_stmts @ inhale_stmts
              | [], _ -> exhale_stmts @ inhale_stmts @ [ reassign_lhs_stmt ]
              | _, [] -> (bind_stmt :: exhale_stmts) @ inhale_stmts
              | _, _ -> (bind_stmt :: exhale_stmts) @ inhale_stmts @ [ reassign_lhs_stmt ])
          in

          Rewriter.return new_stmt
      | FuncDef _ ->
          (* No exhale here: func/pred/invariant contracts can't carry a `requires`
             (see [CallableTyping.check]), so there is nothing to
             check at this call site. *)
          let ret_typ =
            Type.mk_prod stmt.stmt_loc
              (List.map call_decl.call_decl_returns ~f:(fun var_decl -> var_decl.var_type))
          in

          let new_assign_stmt =
            Stmt.mk_assign ~loc:stmt.stmt_loc
              (List.map new_lhs_list ~f:Expr.to_qual_ident)
              (Expr.mk_app ~loc:stmt.stmt_loc ~typ:ret_typ (Expr.Var call_desc.call_name)
                 call_desc.call_args)
          in

          let reassign_lhs_stmt =
            Stmt.mk_assign ~loc:stmt.stmt_loc
              (List.map lhs_list ~f:(fun decl -> QualIdent.from_ident decl.var_name))
              (Expr.mk_tuple new_lhs_list)
          in

          let new_stmt =
            Stmt.mk_block_stmt ~loc:stmt.stmt_loc
              (match lhs_list with
              | [] -> [ new_assign_stmt ]
              | _ -> [ new_assign_stmt; reassign_lhs_stmt ])
          in

          Rewriter.return new_stmt)
  | _ -> Rewriter.Stmt.descend stmt ~f:rewrite_call_stmts

let rewrite_callable_pre_post_conds (c : Callable.t) : Callable.t Rewriter.t =
  let open Rewriter.Syntax in
  match c.call_def with
  | ProcDef proc -> (
      match proc.proc_body with
      | None -> Rewriter.return c
      | Some body ->
          let loc = Stmt.to_loc body in
          let* own_qual_ident = Rewriter.current_scope_id in
          let num_precond = List.length c.call_decl.call_decl_precond in
          let pre_conds =
            List.filter_mapi c.call_decl.call_decl_precond ~f:(fun i spec ->
                if spec.spec_atomic then None
                else
                  let spec = { spec with spec_source = Some (own_qual_ident, i) } in
                  Some
                    (Stmt.mk_inhale_spec
                       ~cmnt:("precond: " ^ Expr.to_string spec.spec_form)
                       ~loc:(Expr.to_loc spec.spec_form) spec))
          and post_conds =
            List.filter_mapi c.call_decl.call_decl_postcond ~f:(fun j spec ->
                if spec.spec_atomic then None
                else
                  let spec =
                    { spec with spec_source = Some (own_qual_ident, num_precond + j) }
                  in
                  Some
                    (Stmt.mk_exhale_spec
                       ~cmnt:("postcond: " ^ Expr.to_string spec.spec_form)
                       ~loc:(Stmt.to_loc body |> Loc.to_end)
                       spec))
          in

          let* pre_conds, post_conds =
            if not (Callable.is_atomic c.call_decl) then
              Rewriter.return (pre_conds, post_conds)
            else
              let* callable_fully_qual_name = Rewriter.current_scope_id in

              let atomic_token_var =
                Expr.mk_var
                  ~typ:(Type.atomic_token callable_fully_qual_name)
                  (QualIdent.from_ident
                     (ProgUtils.callable_au_token_ident ~loc c.call_decl.call_decl_name))
              in

              let concrete_args =
                List.filter c.call_decl.call_decl_formals ~f:(fun var_decl ->
                    not var_decl.var_implicit)
              in
              let concrete_args_expr = List.map concrete_args ~f:Expr.from_var_decl in

              let inhale_au =
                Stmt.mk_inhale_expr ~cmnt:"au_precond" ~loc
                  (Expr.mk_app ~loc ~typ:Type.perm (Expr.AUPred callable_fully_qual_name)
                     [ atomic_token_var; Expr.mk_tuple concrete_args_expr ])
              in

              let exhale_au =
                let ret_vars =
                  List.map c.call_decl.call_decl_returns ~f:(fun var_decl ->
                      Expr.from_var_decl var_decl)
                in
                let ret_expr = Expr.mk_tuple ~loc ret_vars in
                let error =
                  ( Error.Verification Error.Uncommitted,
                    loc |> Loc.to_end,
                    "The atomic specification may not have been committed before \
                     reaching this return point" )
                in
                Stmt.mk_exhale_expr ~cmnt:"au_postcond" ~loc
                  ~spec_error:[ Stmt.mk_const_spec_error error ]
                  (Expr.mk_app ~loc ~typ:Type.perm
                     (Expr.AUPredCommit callable_fully_qual_name)
                     [ atomic_token_var; Expr.mk_tuple concrete_args_expr; ret_expr ])
              in

              Rewriter.return (inhale_au :: pre_conds, exhale_au :: post_conds)
          in

          let new_body = Stmt.mk_block_stmt ~loc (pre_conds @ [ body ] @ post_conds) in
          let new_proc =
            Callable.
              {
                call_decl = c.call_decl;
                call_def = ProcDef { proc_body = Some new_body };
              }
          in
          Rewriter.return new_proc)
  | FuncDef func -> Rewriter.return c

let rec rewrite_add_pred_implicit_args (expr : Expr.t) : Expr.t Rewriter.t =
  let open Rewriter.Syntax in
  match expr with
  | App (Var qual_iden, args, expr_attr) ->
      let* symbol = Rewriter.find qual_iden in
      begin match Rewriter.Symbol.orig_symbol symbol with
      | CallDef callable
        when Poly.(
               callable.call_decl.call_decl_kind = Callable.Pred
               || callable.call_decl.call_decl_kind = Callable.Invariant) ->
          let parameters =
            callable.call_decl.call_decl_formals @ callable.call_decl.call_decl_returns
          in
          if List.length parameters = List.length args then Rewriter.return expr
          else
            let dropped_args = List.drop parameters (List.length args) in
            let* dropped_args =
              if List.is_empty (Rewriter.Symbol.subst symbol) then
                Rewriter.return dropped_args
              else
                Rewriter.Symbol.extract symbol ~f:(fun _ requalify _ ->
                    Rewriter.List.map dropped_args
                      ~f:
                        (Rewriter.VarDecl.rewrite_types
                           ~f:(Rewriter.Type.rewrite_qual_idents ~f:requalify)))
            in
            let* () =
              Rewriter.Logs.debug (fun printers m ->
                  m "Lowering.rewrite_add_pred_implicit_args called on: %a"
                    printers.pr_expr expr)
            in
            let new_dropped_args =
              List.map dropped_args ~f:(fun var_decl ->
                  {
                    var_decl with
                    var_name = Ident.fresh expr_attr.expr_loc var_decl.var_name.ident_name;
                    var_loc = expr_attr.expr_loc;
                  })
            in
            Rewriter.return
              (Expr.mk_binder ~loc:expr_attr.expr_loc ~typ:Type.perm Exists
                 new_dropped_args
                 (App
                    ( Var qual_iden,
                      args @ List.map new_dropped_args ~f:Expr.from_var_decl,
                      expr_attr )))
      | _ -> Rewriter.return expr
      end
  | _ -> Rewriter.Expr.descend expr ~f:rewrite_add_pred_implicit_args

let rec rewrite_frac_field_types (symbol : Module.symbol) : Module.symbol Rewriter.t =
  let open Rewriter.Syntax in
  match symbol with
  | ModDef _ | ModInst _ | TypeDef _ | ConstrDef _ | DestrDef _ | VarDef _ | CallDef _ ->
      Rewriter.return symbol
  (* A manifest field shares the target's resource algebra: it takes the
     target's type as already rewritten rather than being wrapped in a Frac of
     its own, which would be a distinct RA over one heap. The field's type feeds
     the Frac module's name (see [rewrite_own_expr_4_arg]), so leaving it as the
     pre-rewrite type derives the wrong name. *)
  | FieldDef ({ field_alias = Some target; _ } as f) ->
      let* target, target_symbol = Rewriter.resolve_and_find target in
      let* target_type = Rewriter.Symbol.reify_type f.field_loc target_symbol in
      (* The alias generates no Frac module of its own, but a name derived from it can
         still be asked for: a callee whose contract was rewritten before this module
         existed carries `<A>.Frac$f` with `A` substituted to the alias's module, and
         nothing re-derives it from the resolved field at that point. Register the name
         as another spelling of the target's, the same way the field itself is
         registered as another spelling of the target. *)
      let* () =
        let* is_field_an_ra = ProgUtils.is_ra_type (Type.field_val target_type) in
        let target_frac_mod =
          ProgUtils.frac_field_to_frac_mod_qual_ident ~loc:f.field_loc target target_type
        in
        (* A target from a unit lowered earlier, such as the library, has already been
           rewritten to its Frac module's type, so it has a Frac module despite looking
           like a resource algebra. *)
        let* already_rewritten = Rewriter.resolve_opt target_frac_mod in
        if is_field_an_ra && Option.is_none already_rewritten then Rewriter.return ()
        else
          Rewriter.add_transparent
            (ProgUtils.frac_field_to_frac_mod_ident ~loc:f.field_loc f.field_name
               target_type)
            target_frac_mod
      in
      Rewriter.return (Module.FieldDef { f with field_type = target_type })
  | FieldDef f ->
      let* is_field_an_ra = ProgUtils.is_ra_type (Type.field_val f.field_type) in

      let* () =
        Rewriter.Logs.debug (fun printers m ->
            m "Lowering.rewrite_frac_field_types:\n          is_field_an_ra: %a -> %b"
              printers.pr_type f.field_type is_field_an_ra)
      in

      if is_field_an_ra then Rewriter.return symbol
      else
        let* field_type = !Rewriter.expand_type_expr_ref f.field_type in
        let field_underlying_tp =
          match field_type with
          | App (Fld, [ tp_expr ], _) -> tp_expr
          | _ -> Error.type_error f.field_loc "Expected field identifier."
        in

        (* A field with a constraint gets the fractional algebra whose validity includes it. *)
        let* frac_def =
          match f.field_constraint with
          | None ->
              let+ tp_module =
                ProgUtils.intros_type_module ~loc:f.field_loc ~f:Typing.check_symbol
                  field_underlying_tp
              in
              (Predefs.lib_frac_mod_qual_ident, [ Module.ModArg tp_module ])
          | Some constr ->
              let+ constraint_module =
                ProgUtils.intros_constraint_module ~loc:f.field_loc ~f:Typing.check_symbol
                  f.field_name field_underlying_tp constr
              in
              ( Predefs.lib_constrained_frac_mod_qual_ident,
                [ Module.ModArg constraint_module ] )
        in

        let instantiated_frac_module =
          Module.ModInst
            (Module.mk_mod_inst
               ~name:
                 (ProgUtils.frac_field_to_frac_mod_ident ~loc:f.field_loc f.field_name
                    field_type)
               ~typ:Predefs.lib_cancellative_ra_mod_qual_ident ~def:frac_def
               ~loc:f.field_loc ())
        in

        (* let* topscope_name = ProgUtils.find_highest_valid_scope_type_expr f.field_loc field_underlying_tp in

           let topscope_name = match topscope_name with
             | Some topscope_name -> topscope_name
             | None -> Error.type_error f.field_loc ("Could not find a valid scope to add field " ^ (Ident.to_string f.field_name) ^ " to.")

           in *)
        let* frac_mod_name =
          Rewriter.introduce_typecheck_symbol ~loc:f.field_loc ~f:Typing.check_symbol
            instantiated_frac_module
        in

        Logs.debug (fun m ->
            m "Lowering.rewrite_frac_field_types: \n          frac_mod_name: %a"
              QualIdent.pr frac_mod_name);

        let frac_type =
          Type.mk_fld f.field_loc
            (Type.mk_var (QualIdent.append frac_mod_name (Ident.make f.field_loc "T" 0)))
        in

        Rewriter.return (Module.FieldDef { f with field_type = frac_type })

(** Settle how each symbol an expression names is spelled, now that the resource algebras
    and heap utilities a field needs have been generated.

    Those artifacts are generated per field and named after it, so they exist only under
    the name of the field they belong to. A manifest field has none of its own -- it
    shares the ones belonging to the field it stands for -- and reaches them through
    aliases registered beside it. That is enough for the front end, which resolves; it is
    not enough for the backend, which keys on the name it is handed. A contract reaching a
    call site through a functor instantiated at a module with a manifest field is exactly
    that case: reifying the callee substitutes its formal for the argument module
    syntactically, so the contract comes out naming `Adapt.Frac$f` for a resource algebra
    that only ever existed as `Client.Frac$bit`.

    Only qualified names are touched -- an unqualified one is a formal or a local, which
    resolution has no business rewriting -- and anything that does not resolve is left
    exactly as it was. Types are left alone: they are canonical already, having been
    expanded on the way here. *)
let canonicalize_symbols (expr : Expr.t) : Expr.t Rewriter.t =
  let open Rewriter.Syntax in
  let canonicalize qual_ident =
    if List.is_empty (QualIdent.path qual_ident) then Rewriter.return qual_ident
    else
      let+ resolved = Rewriter.resolve_opt qual_ident in
      Option.value resolved ~default:qual_ident
  in
  Rewriter.Expr.rewrite_qual_idents_m ~f:canonicalize expr

let rec rewrite_own_expr_4_arg (expr : Expr.t) : Expr.t Rewriter.t =
  (* Rewrites expressions of the form `own(x, f, v, p)` to `own (x, f, Frac[f.type].frac_chunk(v, p))

     Essentially, makes a uniform 3-arg representation of all own expressions, frac-type as well as RA type.
  *)
  let open Rewriter.Syntax in
  let* () =
    Rewriter.Logs.debug (fun printers m ->
        m "Lowering.rewrite_own_expr_4_arg: run on expr: %a" printers.pr_expr expr)
  in

  match expr with
  | App (Own, [ expr1; expr2; expr3; expr4 ], expr_attr) ->
      let* () =
        Rewriter.Logs.debug (fun printers m ->
            m "Lowering.rewrite_own_expr_4_arg: found expr: %a" printers.pr_expr expr)
      in

      (* let field_type = match Expr.to_type expr2 with
           | App (Fld, [tp_expr], _) -> tp_expr
           | _ -> Error.type_error (Expr.to_loc expr2) "Expected field identifier."
         in *)
      let field_type = Expr.to_type expr2 in

      let* () =
        Rewriter.Logs.debug (fun printers m ->
            m "Lowering.rewrite_own_expr_4_arg: field_type1: %a" printers.pr_type
              field_type)
      in

      let* field_type = !Rewriter.expand_type_expr_ref field_type in
      let field_name = QualIdent.unqualify (Expr.to_qual_ident expr2) in

      let* () =
        Rewriter.Logs.debug (fun printers m ->
            m "Lowering.rewrite_own_expr_4_arg: field_type2: %a" printers.pr_type
              field_type)
      in

      let+ expr3 =
        let expr3_1 = expr3 in
        let expr3_2 = expr4 in

        let* () =
          Rewriter.Logs.debug (fun printers m ->
              m
                "Lowering.rewrite_own_expr_4_arg: intros_type_module started: tp_module: \
                 %a;\n\
                \ ... & frac_mod_ident: %a"
                printers.pr_type field_type QualIdent.pr
                (QualIdent.from_ident
                   (ProgUtils.frac_field_to_frac_mod_ident ~loc:(Expr.to_loc expr)
                      field_name field_type)))
        in

        let* frac_mod_name =
          (* Resolve the field before deriving its Frac module's name. A callee's
             contract reaches here with the instantiation substitution already
             applied syntactically (`H.f` -> `Adapt.f`), so the name was never put
             through the symbol table; without this a manifest field would look
             for an RA module beside the alias rather than beside the field it
             stands for. *)
          let* field_qual_ident = Rewriter.resolve (Expr.to_qual_ident expr2) in
          let frac_mod_name =
            ProgUtils.frac_field_to_frac_mod_qual_ident ~loc:(Expr.to_loc expr)
              field_qual_ident field_type
          in

          Logs.debug (fun m ->
              m "Lowering.rewrite_own_expr_4_args:  \n            frac_mod_name: %a"
                QualIdent.pr frac_mod_name);

          Rewriter.resolve frac_mod_name
        in

        let frac_type =
          Type.mk_var
            (QualIdent.append frac_mod_name (Ident.make (Expr.to_loc expr) "T" 0))
        in
        (* let frac_constr = Rewriter.find_and_reify (Expr.to_loc expr) (QualIdent.append frac_mod_name (Ident.make (Expr.to_loc expr) "frac_chunk" 0)) in *)
        let expr3 =
          Expr.mk_app ~loc:(Expr.to_loc expr) ~typ:frac_type
            (Expr.DataConstr
               (QualIdent.append frac_mod_name
                  (Ident.make (Expr.to_loc expr) "frac_chunk" 0)))
            [ expr3_1; expr3_2 ]
        in

        let* () =
          Rewriter.Logs.debug (fun printers m ->
              m "Lowering.rewrite_own_expr_4_arg:\n            expr3: %a" printers.pr_expr
                expr3)
        in

        Rewriter.return expr3
      in

      Expr.App (Own, [ expr1; expr2; expr3 ], expr_attr)
  | _ -> Rewriter.Expr.descend expr ~f:rewrite_own_expr_4_arg

let rec rewrite_new_fpu_stmt_heap_arg (stmt : Stmt.t) : Stmt.t Rewriter.t =
  let open Rewriter.Syntax in
  (* Logs.debug (fun m -> m "Lowering.rewrite_new_fpu_stmt_heap_arg: stmt: %a" Stmt.pr stmt); *)
  match stmt.stmt_desc with
  | Basic (New new_desc) ->
      let* new_args =
        Rewriter.List.map new_desc.new_args ~f:(fun (field_name, expr_optn) ->
            match expr_optn with
            | None -> Rewriter.return (field_name, expr_optn)
            | Some expr ->
                let* expr_typ = !Rewriter.expand_type_expr_ref (Expr.to_type expr) in

                let* field_symbol = Rewriter.find field_name in
                let* field_elem_type =
                  Rewriter.Symbol.reify_field_type (Expr.to_loc expr) field_symbol
                in

                let* field_elem_typ_expanded =
                  !Rewriter.expand_type_expr_ref field_elem_type
                in

                if Type.(expr_typ = field_elem_typ_expanded) then
                  Rewriter.return (field_name, expr_optn)
                else
                  let frac_mod_name =
                    match field_elem_type with
                    | App (Var qual_iden, _, _) -> QualIdent.pop qual_iden
                    | _ ->
                        Error.type_error (Expr.to_loc expr) "Expected field identifier."
                  in

                  let frac_type =
                    Type.mk_var
                      (QualIdent.append frac_mod_name
                         (Ident.make (Expr.to_loc expr) "T" 0))
                  in
                  let new_expr =
                    Expr.mk_app ~loc:(Expr.to_loc expr) ~typ:frac_type
                      (Expr.DataConstr
                         (QualIdent.append frac_mod_name
                            (Ident.make (Expr.to_loc expr) "frac_chunk" 0)))
                      [ expr; Expr.mk_real 1.0 ]
                  in

                  Rewriter.return (field_name, Some new_expr))
      in

      Rewriter.return { stmt with stmt_desc = Basic (New { new_desc with new_args }) }
  | Basic (Fpu fpu_desc) ->
      let* field_symbol = Rewriter.find fpu_desc.fpu_field in
      let* field_elem_type =
        match Rewriter.Symbol.orig_symbol field_symbol with
        | FieldDef { field_type = App (Fld, [ _ ], _); _ } ->
            Rewriter.Symbol.reify_field_type stmt.stmt_loc field_symbol
        | FieldDef _ -> Error.type_error stmt.stmt_loc "Expected field identifier."
        | _ -> Error.internal_error stmt.stmt_loc "expected a field_def"
      in
      let* field_elem_typ_expanded = !Rewriter.expand_type_expr_ref field_elem_type in
      let compute_new_expr old_expr =
        let loc = Expr.to_loc old_expr in
        let* expr_typ = !Rewriter.expand_type_expr_ref (Expr.to_type old_expr) in

        if Type.(expr_typ = field_elem_typ_expanded) then Rewriter.return old_expr
        else
          let frac_mod_name =
            match field_elem_type with
            | App (Var qual_iden, _, _) -> QualIdent.pop qual_iden
            | _ -> Error.type_error loc "Expected field identifier."
          in

          let frac_type =
            Type.mk_var (QualIdent.append frac_mod_name (Ident.make loc "T" 0))
          in
          let new_expr =
            Expr.mk_app ~loc ~typ:frac_type
              (Expr.DataConstr
                 (QualIdent.append frac_mod_name (Ident.make loc "frac_chunk" 0)))
              [ old_expr; Expr.mk_real 1.0 ]
          in

          Rewriter.return new_expr
      in

      let* fpu_old_val =
        match fpu_desc.fpu_old_val with
        | None -> Rewriter.return None
        | Some expr ->
            let+ new_expr = compute_new_expr expr in
            Some new_expr
      in

      let* fpu_new_val = compute_new_expr fpu_desc.fpu_new_val in

      let new_fpu_desc = { fpu_desc with fpu_old_val; fpu_new_val } in

      Rewriter.return { stmt with stmt_desc = Basic (Fpu new_fpu_desc) }
  | _ -> Rewriter.Stmt.descend stmt ~f:rewrite_new_fpu_stmt_heap_arg

(* Adds a lemma checking that two instances of a predicate or invariant held at
   the same time agree on their implicit parameters if they agree on the explicit
   ones. *)
let rewrite_add_predicate_validity_lemmas (c : Callable.t) : Callable.t Rewriter.t =
  let open Rewriter.Syntax in
  if is_free c.call_decl.call_decl_status then Rewriter.return c
  else
    match c.call_decl.call_decl_kind with
    | Pred | Invariant -> (
        match (c.call_decl.call_decl_returns, c.call_def) with
        | [], _ | _, FuncDef { func_body = None } -> Rewriter.return c
        | rets, FuncDef { func_body = Some body } ->
            let pred_valid_lemma_ident =
              Ident.fresh_member ~owned:false c.call_decl.call_decl_loc
                ("pred_valid$" ^ Ident.to_string c.call_decl.call_decl_name)
            in

            let formal_args, renaming_map1, renaming_map2, postconds =
              let renamings, explicit_args =
                List.fold_map c.call_decl.call_decl_formals
                  ~init:(Map.empty (module QualIdent))
                  ~f:(fun acc_renamings var_decl ->
                    let new_var_decl =
                      {
                        var_decl with
                        var_name =
                          Ident.fresh var_decl.var_loc var_decl.var_name.ident_name;
                      }
                    in
                    let new_var_expr = Expr.from_var_decl new_var_decl in

                    ( Map.add_exn acc_renamings
                        ~key:(QualIdent.from_ident var_decl.var_name)
                        ~data:new_var_expr,
                      new_var_decl ))
              in

              let renamings1, implicit_args1 =
                List.fold_map rets ~init:renamings ~f:(fun acc_renamings var_decl ->
                    let new_var_decl =
                      {
                        var_decl with
                        var_name =
                          Ident.fresh var_decl.var_loc var_decl.var_name.ident_name;
                      }
                    in
                    let new_var_expr = Expr.from_var_decl new_var_decl in

                    ( Map.add_exn acc_renamings
                        ~key:(QualIdent.from_ident var_decl.var_name)
                        ~data:new_var_expr,
                      new_var_decl ))
              in

              let renamings2, implicit_args2 =
                List.fold_map rets ~init:renamings ~f:(fun acc_renamings var_decl ->
                    let new_var_decl =
                      {
                        var_decl with
                        var_name =
                          Ident.fresh var_decl.var_loc var_decl.var_name.ident_name;
                      }
                    in
                    let new_var_expr = Expr.from_var_decl new_var_decl in

                    ( Map.add_exn acc_renamings
                        ~key:(QualIdent.from_ident var_decl.var_name)
                        ~data:new_var_expr,
                      new_var_decl ))
              in

              let postconds =
                List.map2_exn implicit_args1 implicit_args2
                  ~f:(fun implicit_arg1 implicit_arg2 ->
                    let spec_expr =
                      Expr.mk_eq ~loc:(Expr.to_loc body)
                        (Expr.from_var_decl implicit_arg1)
                        (Expr.from_var_decl implicit_arg2)
                    in
                    let error =
                      ( Error.Verification Error.Implicit_agreement,
                        implicit_arg1.var_loc,
                        "Two instances held at the same time that agree on the explicit \
                         parameters may disagree on this implicit parameter" )
                    in
                    Stmt.mk_spec ~spec_error:[ (fun _ _ -> error) ] spec_expr)
              in

              ( explicit_args @ implicit_args1 @ implicit_args2,
                renamings1,
                renamings2,
                postconds )
            in

            (*let postcond =
            let error = (Error.Verification, 
             (Expr.mk_bool ~loc:(Expr.to_loc body) false)
          in*)
            let call_decl =
              Callable.mk_call_decl ~kind:Lemma ~name:pred_valid_lemma_ident
                ~loc:c.call_decl.call_decl_loc ~formals:formal_args ~postcond:postconds
                ~needs_mask:[] ~grants_mask:[] ()
            in

            let* pred_qual_ident = Rewriter.current_scope_id in

            let call_body =
              Stmt.mk_block_stmt ~loc:c.call_decl.call_decl_loc
                [
                  Stmt.mk_inhale_expr ~loc:c.call_decl.call_decl_loc
                    ~spec_source:(pred_qual_ident, 0)
                    (Expr.alpha_renaming body renaming_map1);
                  Stmt.mk_inhale_expr ~loc:c.call_decl.call_decl_loc
                    ~spec_source:(pred_qual_ident, 0)
                    (Expr.alpha_renaming body renaming_map2);
                ]
            in

            let call_def =
              Module.CallDef
                Callable.{ call_decl; call_def = ProcDef { proc_body = Some call_body } }
            in

            let* _ =
              Rewriter.introduce_typecheck_symbol ~loc:c.call_decl.call_decl_loc
                ~f:Typing.check_symbol call_def
            in

            Rewriter.return c
        | _, ProcDef _ ->
            Error.internal_error c.call_decl.call_decl_loc
              "Expected a function definition for a predicate")
    | _ -> Rewriter.return c

let rewrite_introduce_heaps (c : Callable.t) : Callable.t Rewriter.t =
  let open Rewriter.Syntax in
  Logs.debug (fun m ->
      m "Lowering.rewrite_introduce_heaps: Introducing heaps in callable: %a" Ident.pr
        c.call_decl.call_decl_name);
  match c.call_def with
  | FuncDef _ -> Rewriter.return c
  | ProcDef { proc_body = None } -> Rewriter.return c
  | ProcDef { proc_body = Some body } ->
      let* preds_list = ProgUtils.stmt_preds_mentioned body in
      let* ext_hooks = Rewriter.current_ext_hooks in
      let fields_list =
        Stmt.make_stmt_fields_accessed
          ~basic_stmt_ext_fields_accessed:ext_hooks.basic_stmt_ext_fields_accessed
          ~stmt_ext_fields_accessed:ext_hooks.stmt_ext_fields_accessed body
      in
      let au_preds_list = Set.to_list (Stmt.stmt_au_preds_referenced body) in

      Logs.debug (fun m ->
          m "Lowering.rewrite_introduce_heaps: Predicates mentioned in the body");

      let* body =
        HeapsExplicitTrnsl.introduce_heaps_in_stmts ~loc:c.call_decl.call_decl_loc
          ~fields_list ~preds_list ~au_preds_list body
      in

      Rewriter.return { c with call_def = ProcDef { proc_body = Some body } }

(** The current version of each variable in [var_map], one per source name. A loop's
    procedure has its variables twice, as parameters and as returns; the version that was
    assigned is the current one, or, if neither was, the one declared first. *)
let current_versions (var_map : var_decl ident_map) : var_decl list =
  Map.to_alist var_map
  |> List.sort_and_group ~compare:(fun (v1, _) (v2, _) ->
      String.compare (Ident.name v1) (Ident.name v2))
  |> List.map ~f:(fun versions ->
      let assigned =
        List.find versions ~f:(fun (source, (current : var_decl)) ->
            not (Ident.equal source current.var_name))
      in
      snd (Option.value assigned ~default:(List.hd_exn versions)))

type ssa_state = {
  ssa_versions : var_decl ident_map;
  ssa_substitutions : expr qual_ident_map;
}

let empty_ssa_state =
  {
    ssa_versions = Map.empty (module Ident);
    ssa_substitutions = Map.empty (module QualIdent);
  }

let set_ssa_version state source current =
  {
    ssa_versions = Map.set state.ssa_versions ~key:source ~data:current;
    ssa_substitutions =
      Map.set state.ssa_substitutions ~key:(QualIdent.from_ident source)
        ~data:(Expr.from_var_decl current);
  }

let declare_ssa_version state source =
  let open Rewriter.Syntax in
  let old = Map.find_exn state.ssa_versions source in
  let current = { old with var_name = Ident.fresh old.var_loc old.var_name.ident_name } in
  let+ () =
    Rewriter.introduce_symbol
      (VarDef { var_decl = current; var_init = None; var_is_free = NotFree })
  in
  (set_ssa_version state source current, current)

let fresh_ssa_version source =
  let open Rewriter.Syntax in
  let* state = Rewriter.current_user_state in
  let* state, current = declare_ssa_version state source in
  let+ () = Rewriter.set_user_state state in
  QualIdent.from_ident current.var_name

let rec rewrite_ssa_stmts (s : Stmt.t) : (Stmt.t, ssa_state) Rewriter.t_ext =
  let open Rewriter.Syntax in
  let* entry = Rewriter.current_user_state in
  let subst_map = entry.ssa_substitutions in
  match s.stmt_desc with
  | Basic basic_stmt -> (
      match basic_stmt with
      | Spec (spec_kind, spec) ->
          let spec_form = Expr.alpha_renaming spec.spec_form subst_map in
          (* Where an assertion is checked, the current versions of the variables, which a
             counterexample is read from. *)
          let spec_state =
            match spec_kind with
            | Assert -> current_versions entry.ssa_versions
            | _ -> spec.spec_state
          in
          Rewriter.return
            Stmt.
              {
                s with
                stmt_desc = Basic (Spec (spec_kind, { spec with spec_form; spec_state }));
              }
      | Assign assign_stmt ->
          let assign_rhs = Expr.alpha_renaming assign_stmt.assign_rhs subst_map in
          let* assign_lhs =
            if assign_stmt.assign_is_init then Rewriter.return assign_stmt.assign_lhs
            else
              Rewriter.List.map assign_stmt.assign_lhs ~f:(fun qual_ident ->
                  let local_var = QualIdent.to_ident qual_ident in
                  let* () =
                    Rewriter.Logs.debug (fun printers m ->
                        m
                          "Lowering.rewrite_ssa_stmts: Assigning to local variable %a; \
                           for stmt %a"
                          Ident.pr local_var printers.pr_stmt s)
                  in
                  fresh_ssa_version local_var)
          in
          Rewriter.return
            Stmt.
              {
                s with
                stmt_desc = Basic (Assign { assign_stmt with assign_lhs; assign_rhs });
              }
      | Havoc hvc ->
          if not (QualIdent.is_local hvc.havoc_var) then assert false
          else if hvc.havoc_is_init then Rewriter.return (Stmt.mk_skip ~loc:s.stmt_loc)
          else
            let local_var = QualIdent.to_ident hvc.havoc_var in
            Logs.debug (fun m ->
                m "Lowering.rewrite_ssa_stmts: Havocing local variable %a" Ident.pr
                  local_var);
            let+ _ = fresh_ssa_version local_var in
            Stmt.mk_block_stmt ~loc:s.stmt_loc []
      | Bind bind_stmt ->
          let* bind_lhs =
            Rewriter.List.map bind_stmt.bind_lhs ~f:(fun qual_ident ->
                fresh_ssa_version (QualIdent.unqualify qual_ident))
          in
          let* state = Rewriter.current_user_state in
          let spec_form =
            Expr.alpha_renaming bind_stmt.bind_rhs.spec_form state.ssa_substitutions
          in
          let bind_rhs = { bind_stmt.bind_rhs with spec_form } in
          Rewriter.return Stmt.{ s with stmt_desc = Basic (Bind { bind_lhs; bind_rhs }) }
      | _ ->
          let* () =
            Rewriter.Logs.debug (fun printers m ->
                m "Lowering.rewrite_ssa_stmts: Skipping statement %a" printers.pr_stmt s)
          in
          assert false)
  | Block block_stmt ->
      let+ block_body = Rewriter.List.map block_stmt.block_body ~f:rewrite_ssa_stmts in
      Stmt.mk_block_stmt ~kind:block_stmt.block_kind ~loc:s.stmt_loc block_body
  | Cond cond_stmt when not cond_stmt.cond_if_assumes_false ->
      let cond_test =
        Option.map ~f:(fun test -> Expr.alpha_renaming test subst_map) cond_stmt.cond_test
      in
      let* cond_then = rewrite_ssa_stmts cond_stmt.cond_then in
      let* then_state = Rewriter.current_user_state in
      let* () = Rewriter.set_user_state entry in
      let* cond_else = rewrite_ssa_stmts cond_stmt.cond_else in
      let* else_state = Rewriter.current_user_state in
      let updated_vals =
        Map.fold2 then_state.ssa_versions else_state.ssa_versions ~init:[]
          ~f:(fun ~key ~data acc ->
            match data with
            | `Both (then_var_decl, else_var_decl) ->
                if Ident.equal then_var_decl.var_name else_var_decl.var_name then acc
                else key :: acc
            | `Left _ | `Right _ ->
                Error.error s.stmt_loc
                  "Mismatched variable declarations in then and else branches.")
      in
      let* merged =
        Rewriter.List.fold_left updated_vals ~init:entry ~f:(fun state var ->
            let+ state, _ = declare_ssa_version state var in
            state)
      in
      let join_assignments state =
        List.map updated_vals ~f:(fun var ->
            let old = Map.find_exn state.ssa_versions var in
            let current = Map.find_exn merged.ssa_versions var in
            Stmt.mk_assign ~loc:s.stmt_loc
              [ QualIdent.from_ident current.var_name ]
              (Expr.from_var_decl old))
      in
      let cond_then =
        Stmt.mk_block_stmt ~loc:s.stmt_loc (cond_then :: join_assignments then_state)
      in
      let cond_else =
        Stmt.mk_block_stmt ~loc:s.stmt_loc (cond_else :: join_assignments else_state)
      in
      let+ () = Rewriter.set_user_state merged in
      Stmt.
        {
          s with
          stmt_desc =
            Cond { cond_test; cond_then; cond_else; cond_if_assumes_false = false };
        }
  | Cond cond_stmt ->
      assert cond_stmt.cond_if_assumes_false;
      assert (
        Poly.(
          cond_stmt.cond_else.stmt_desc = Block { block_kind = Regular; block_body = [] }));
      let cond_test =
        Option.map ~f:(fun test -> Expr.alpha_renaming test subst_map) cond_stmt.cond_test
      in
      let* cond_then = rewrite_ssa_stmts cond_stmt.cond_then in
      let* cond_else = rewrite_ssa_stmts cond_stmt.cond_else in
      let+ () = Rewriter.set_user_state entry in
      Stmt.
        {
          s with
          stmt_desc =
            Cond { cond_test; cond_then; cond_else; cond_if_assumes_false = true };
        }
  | Loop _ | StmtExt _ -> assert false

let rewrite_ssa_transform (c : Callable.t) : (Callable.t, ssa_state) Rewriter.t_ext =
  let open Rewriter.Syntax in
  match c.call_def with
  | FuncDef _ | ProcDef { proc_body = None } -> Rewriter.return c
  | ProcDef { proc_body = Some body } ->
      let* () =
        Rewriter.Logs.debug (fun printers m ->
            m "rewrite_ssa_transform: init_map: %a"
              (Util.Print.pr_list_comma printers.pr_type_var_decl)
              (c.call_decl.call_decl_formals @ c.call_decl.call_decl_returns
             @ c.call_decl.call_decl_locals))
      in
      let versions =
        List.fold
          (c.call_decl.call_decl_formals @ c.call_decl.call_decl_returns
         @ c.call_decl.call_decl_locals)
          ~init:(Map.empty (module Ident))
          ~f:(fun map var_decl -> Map.add_exn map ~key:var_decl.var_name ~data:var_decl)
      in
      let substitutions =
        Map.fold versions
          ~init:(Map.empty (module QualIdent))
          ~f:(fun ~key ~data map ->
            Map.add_exn map ~key:(QualIdent.from_ident key)
              ~data:(Expr.from_var_decl data))
      in
      let* () =
        Rewriter.set_user_state
          { ssa_versions = versions; ssa_substitutions = substitutions }
      in
      let* () =
        Rewriter.Logs.debug (fun printers m ->
            m "Lowering.rewrite_ssa_transform: Starting rewrites on callable %a"
              printers.pr_callable c)
      in
      let+ body = rewrite_ssa_stmts body in
      { c with call_def = ProcDef { proc_body = Some body } }

let rec rewrite_assign_stmts (s : Stmt.t) : Stmt.t Rewriter.t =
  let open Rewriter.Syntax in
  let* () =
    Rewriter.Logs.debug (fun printers m ->
        m "Lowering.rewrite_assign_stmts: Starting rewrites on statement %a"
          printers.pr_stmt s)
  in

  match s.stmt_desc with
  | Basic (Assign assign_stmt) ->
      let+ assign_lhs =
        Rewriter.List.map assign_stmt.assign_lhs ~f:(fun qual_ident ->
            let* qual_ident, symbol = Rewriter.resolve_and_find qual_ident in
            let+ typ = Rewriter.Symbol.reify_type s.stmt_loc symbol in
            Expr.mk_var ~typ qual_ident)
      in

      let assume_stmt =
        Stmt.mk_assume_expr ~loc:s.stmt_loc
          (Expr.mk_eq (Expr.mk_tuple assign_lhs) assign_stmt.assign_rhs)
      in

      assume_stmt
  | _ -> let* s = Rewriter.Stmt.descend s ~f:rewrite_assign_stmts in

         Rewriter.return s

let lower (m : Module.t) : (Module.t * CallGraph.Graph.t) Rewriter.t =
  let open Rewriter.Syntax in
  Logs.debug (fun m1 ->
      m1 "Lowering.lower: Starting rewrite_fold_unfold_stmts on module %a" Ident.pr
        m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_stmts ~f:rewrite_fold_unfold_stmts m in

  let* tbl = Rewriter.get_table in
  let lemma_calls = CallGraph.lemma_calls tbl m in

  Logs.debug (fun m1 ->
      m1 "Lowering.lower: Starting rewrite_call_stmts on module %a" Ident.pr
        m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_stmts ~f:rewrite_call_stmts m in

  Logs.debug (fun m1 ->
      m1 "Lowering.lower: Starting rewrite_ret_stmts on module %a" Ident.pr
        m.mod_decl.mod_decl_name);
  let* m =
    Rewriter.Module.rewrite_callables
      ~f:(fun callable ->
        Rewriter.Callable.rewrite_stmts ~f:(rewrite_ret_stmts callable.call_decl) callable)
      m
  in

  Logs.debug (fun m1 ->
      m1 "Lowering.lower: Starting rewrite_frac_field_types on module %a" Ident.pr
        m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rec_rewrite_symbols ~f:rewrite_frac_field_types m in

  let* () =
    Rewriter.Logs.debug (fun _ m1 ->
        m1 "Lowering.lower: Starting canonicalize_symbols on module %a" Ident.pr
          m.mod_decl.mod_decl_name)
  in
  let* m = Rewriter.Module.rewrite_expressions ~f:canonicalize_symbols m in

  Logs.debug (fun m1 ->
      m1 "Lowering.lower: Starting rewrite_own_expr_4_arg on module %a" Ident.pr
        m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_expressions ~f:rewrite_own_expr_4_arg m in

  Logs.debug (fun m1 ->
      m1 "Lowering.lower: Starting rewrite_new_fpu_stmt_heap_arg on module %a" Ident.pr
        m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_stmts ~f:rewrite_new_fpu_stmt_heap_arg m in

  Logs.debug (fun m1 ->
      m1 "Lowering.lower: Starting rewrite_new_stmts on module %a" Ident.pr
        m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_stmts ~f:rewrite_new_stmts m in

  Logs.debug (fun m1 ->
      m1 "Lowering.lower: Starting rewrite_add_predicate_validity_lemmas on module %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_callables ~f:rewrite_add_predicate_validity_lemmas m in

  Logs.debug (fun m1 ->
      m1 "Lowering.lower: Starting rewrite_callable_pre_post_conds on module %a" Ident.pr
        m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_callables ~f:rewrite_callable_pre_post_conds m in

  Logs.debug (fun m1 ->
      m1 "Lowering.lower: Starting rewrite_add_pred_implicit_args on module %a" Ident.pr
        m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_expressions ~f:rewrite_add_pred_implicit_args m in

  Logs.debug (fun m1 ->
      m1 "Lowering.lower: Starting rewrite_add_field_utils on module %a" Ident.pr
        m.mod_decl.mod_decl_name);
  let* m =
    Rewriter.Module.rec_rewrite_symbols ~f:HeapsExplicitTrnsl.rewrite_add_field_utils m
  in

  Logs.debug (fun m1 ->
      m1 "Lowering.lower: Starting rewrite_add_pred_utils on module %a" Ident.pr
        m.mod_decl.mod_decl_name);
  let* m =
    Rewriter.Module.rewrite_callables ~f:HeapsExplicitTrnsl.rewrite_add_pred_utils m
  in

  Logs.debug (fun m1 ->
      m1 "Lowering.lower: Starting rewrite_add_atomics_utils on module %a" Ident.pr
        m.mod_decl.mod_decl_name);
  let* m =
    Rewriter.Module.rewrite_callables ~f:HeapsExplicitTrnsl.rewrite_add_atomics_utils m
  in

  Logs.debug (fun m1 ->
      m1 "Lowering.lower: Starting structural expression simplification on module %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m =
    Rewriter.Module.rewrite_callables ~f:ExpressionSimplification.rewrite_callable m
  in

  Logs.debug (fun m1 ->
      m1 "Lowering.lower: Starting rewriter_skolemize_inhale_stmts on module %a" Ident.pr
        m.mod_decl.mod_decl_name);
  let* m =
    Rewriter.Module.rewrite_stmts
      ~f:HeapsExplicitTrnsl.TrnslInhale.rewriter_skolemize_inhale_stmts m
  in

  Logs.debug (fun m1 ->
      m1
        "Lowering.lower: Starting rewriter_user_annot_elim_exists_from_exhales on module \
         %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m =
    Rewriter.eval_with_user_state ~init:None
      (Rewriter.Module.rewrite_stmts
         ~f:HeapsExplicitTrnsl.TrnslExhale.rewriter_user_annot_elim_exists_from_exhales m)
  in

  Logs.debug (fun m1 ->
      m1 "Lowering.lower: Starting rewrite_introduce_heaps on module %a" Ident.pr
        m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_callables ~f:rewrite_introduce_heaps m in

  Logs.debug (fun m1 ->
      m1 "Lowering.lower: Starting rewriter_eliminate_binds_for_inhale on module %a"
        Ident.pr m.mod_decl.mod_decl_name);
  let* m =
    Rewriter.eval_with_user_state ~init:None
      (Rewriter.Module.rewrite_stmts
         ~f:HeapsExplicitTrnsl.TrnslInhale.rewriter_eliminate_binds_for_inhale m)
  in

  Logs.debug (fun m1 ->
      m1 "Lowering.lower: Starting rewrite_fpu on module %a" Ident.pr
        m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_stmts ~f:HeapsExplicitTrnsl.rewrite_fpu m in

  Logs.debug (fun m1 ->
      m1 "Lowering.lower: Starting rewrite_binds on module %a" Ident.pr
        m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_stmts ~f:HeapsExplicitTrnsl.rewrite_binds m in

  Logs.debug (fun m1 ->
      m1 "Lowering.lower: Starting rewriter_skolemize_assume_stmts on module %a" Ident.pr
        m.mod_decl.mod_decl_name);
  let* m =
    Rewriter.Module.rewrite_stmts
      ~f:HeapsExplicitTrnsl.TrnslInhale.rewriter_skolemize_assume_stmts m
  in

  Logs.debug (fun m1 ->
      m1 "Lowering.lower: Starting witness computation on module %a" Ident.pr
        m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_stmts ~f:WitnessComputation.rewrite_stmt m in

  Logs.debug (fun m1 ->
      m1 "Lowering.lower: Starting rewrite_make_heaps_explicit on module %a" Ident.pr
        m.mod_decl.mod_decl_name);
  let* m =
    Rewriter.Module.rewrite_stmts ~f:HeapsExplicitTrnsl.rewrite_make_heaps_explicit m
  in

  Logs.debug (fun m1 ->
      m1 "Lowering.lower: Starting rewrite_expand_types on module %a" Ident.pr
        m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_types ~f:rewrite_expand_types m in

  let* () =
    Rewriter.Logs.debug (fun printers m1 ->
        m1 "Lowering.lower: Starting rewrite_ssa_transform on module %a: %a" Ident.pr
          m.mod_decl.mod_decl_name printers.pr_module m)
  in
  let* m =
    Rewriter.eval_with_user_state ~init:empty_ssa_state
      (Rewriter.Module.rewrite_callables ~f:rewrite_ssa_transform m)
  in

  Logs.debug (fun m1 ->
      m1 "Lowering.lower: Starting rewrite_assign_stmts on module %a" Ident.pr
        m.mod_decl.mod_decl_name);
  let* m = Rewriter.Module.rewrite_stmts ~f:rewrite_assign_stmts m in

  let* tbl = Rewriter.get_table in

  (* Logs.debug (fun m -> m "Lowering.lower: SymbolTbl Symbols: \n%a\n" (Util.Print.pr_list_comma (fun ppf (k,v) -> Stdlib.Format.fprintf ppf "%a -> %a" QualIdent.pr k Module.pr_symbol v)) (Map.to_alist (Map.filter_keys tbl.tbl_symbols ~f:(fun k -> Poly.((QualIdent.to_string k) = "$Program.pr"))))); *)
  Rewriter.return (m, lemma_calls)

(** Lowers the front end's output for [m] to what the SMT encoding is generated from:
    calls, folds and returns become inhales and exhales, fields resource algebras, heaps
    explicit, and assignments SSA. Returns the module together with its lemma call graph
    (see [CallGraph.lemma_calls]). Every compilation unit goes through the front end
    before any is lowered (see [Elaboration.elaborate_module]). *)
let lower_module ?(tbl = SymbolTbl.create ()) ?ext_hooks ?diagnostics (m : Module.t) =
  assert (SymbolTbl.curr_is_root tbl);
  let tbl, (m, lemma_calls) = Rewriter.eval ?ext_hooks ?diagnostics (lower m) tbl in
  (tbl, m, lemma_calls)
