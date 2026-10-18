open Base
open Ast
open Util

type occurrence = {
  predicate : qual_ident;
  args : expr list;
  guard : expr;
  strict : bool;
}

let application expr =
  let open Rewriter.Syntax in
  match expr with
  | Expr.App (Var name, args, _)
    when match Expr.to_type expr with Type.App (Perm, _, _) -> true | _ -> false ->
      let* name, symbol = Rewriter.resolve_and_find name in
      let+ symbol = Rewriter.Symbol.reify symbol in
      begin match symbol with
      | Module.CallDef { call_decl = { call_decl_kind = Pred; _ }; _ } -> Some (name, args)
      | _ -> None
      end
  | _ -> Rewriter.return None

let fresh_local ~loc name typ =
  let open Rewriter.Syntax in
  let var = Type.mk_var_decl ~ghost:true ~loc (Ident.fresh loc name) typ in
  let+ () =
    Rewriter.introduce_symbol
      (Module.VarDef { var_decl = var; var_init = None; var_is_free = NotFree })
  in
  var

let snapshot ~loc name expr =
  let open Rewriter.Syntax in
  let+ var = fresh_local ~loc name (Expr.to_type expr) in
  ( Stmt.mk_assign ~loc ~is_init:true [ QualIdent.from_ident var.var_name ] expr,
    Expr.from_var_decl var )

let capture ~loc occurrence =
  let open Rewriter.Syntax in
  let* snapshots =
    Rewriter.List.map occurrence.args ~f:(snapshot ~loc "$induction_arg")
  in
  let+ guard_stmt, guard = snapshot ~loc "$induction_guard" occurrence.guard in
  ( List.map snapshots ~f:fst @ [ guard_stmt ],
    { occurrence with args = List.map snapshots ~f:snd; guard } )

let matches ~loc predicate args occurrence =
  if not (QualIdent.equal predicate occurrence.predicate) then Expr.mk_bool ~loc false
  else
    match List.zip args occurrence.args with
    | Unequal_lengths -> Expr.mk_bool ~loc false
    | Ok pairs ->
        Expr.mk_and ~loc
          (occurrence.guard :: List.map pairs ~f:(fun (a, b) -> Expr.mk_eq ~loc a b))

let progress ~loc predicate args occurrences =
  List.filter occurrences ~f:(fun occurrence -> occurrence.strict)
  |> List.map ~f:(matches ~loc predicate args)
  |> Expr.mk_or ~loc

let rec precondition_occurrences expr =
  match expr with
  | Expr.App (And, exprs, _) -> List.concat_map exprs ~f:precondition_occurrences
  | _ -> [ expr ]

let check_measure call_decl spec =
  let open Rewriter.Syntax in
  let loc = Expr.to_loc spec.Stmt.spec_form in
  let* app = application spec.spec_form in
  match app with
  | None -> Rewriter.return ()
  | Some (name, _) ->
      let* predicate = Rewriter.find_and_reify_callable name in
      let* () =
        match predicate.call_def with
        | FuncDef { func_body = Some _ }
          when (not predicate.call_decl.call_decl_is_inline)
               && List.is_empty predicate.call_decl.call_decl_returns ->
            Rewriter.return ()
        | _ ->
            Error.type_error loc
              "a predicate decreases measure requires a concrete, non-inline predicate \
               without output parameters"
      in
      let* () =
        match call_decl.Callable.call_decl_kind with
        | Proc | Lemma -> Rewriter.return ()
        | Func | Pred | Invariant ->
            Error.type_error loc "predicate decreases measures require a proc or lemma"
      in
      Rewriter.return ()

let check_precondition (call_decl : Callable.call_decl) spec =
  let loc = Expr.to_loc spec.Stmt.spec_form in
  let candidates =
    List.concat_map call_decl.call_decl_precond ~f:(fun spec ->
        precondition_occurrences spec.Stmt.spec_form)
  in
  let count = List.count candidates ~f:(Expr.alpha_equal spec.spec_form) in
  if count = 1 then Rewriter.return ()
  else
    Error.type_error loc
      "a predicate decreases measure must occur exactly once as a top-level chunk of the \
       precondition"

(* Ordinary unfolding forgets which least-fixpoint derivation supplied a chunk.
   Require its children to be determined by parameters and uniquely owned values;
   otherwise an existential choice could repeatedly expose the parent itself. *)
let validate_predicate ~loc root =
  let open Rewriter.Syntax in
  let rec validate visited name =
    if Set.mem visited name then Rewriter.return visited
    else
      let visited = Set.add visited name in
      let* predicate = Rewriter.find_and_reify_callable name in
      let body =
        match predicate.call_def with
        | FuncDef { func_body = Some body } -> body
        | _ ->
            Error.type_error loc
              "structural predicate measures require concrete predicate bodies"
      in
      let bound =
        Expr.existential_vars_type body
        |> Map.keys
        |> List.map ~f:QualIdent.from_ident
        |> Set.of_list (module QualIdent)
      in
      let determined known expr =
        let rec heap_independent = function
          | Expr.App ((Read | ExprExt _), _, _) -> false
          | Expr.App (_, args, _) -> List.for_all args ~f:heap_independent
          | Expr.Binder (_, _, _, body, _) -> heap_independent body
        in
        let variables =
          Expr.signature expr |> Map.keys |> Set.of_list (module QualIdent)
        in
        heap_independent expr && Set.is_subset (Set.inter bound variables) ~of_:known
      in
      let variable = function
        | Expr.App (Var name, [], _) when Set.mem bound name -> Some name
        | _ -> None
      in
      let rec conjuncts = function
        | Expr.App (And, exprs, _) -> List.concat_map exprs ~f:conjuncts
        | Expr.Binder (Exists, _, _, body, _) -> conjuncts body
        | expr -> [ expr ]
      in
      let derive known expr =
        let add target value known =
          match variable target with
          | Some name when determined known value -> Set.add known name
          | _ -> known
        in
        match expr with
        | Expr.App (Eq, [ a; b ], _) -> add b a (add a b known)
        | Expr.App (Own, [ reference; _; value; Expr.App (Real fraction, [], _) ], _)
          when Float.equal fraction 1. && determined known reference ->
            begin match variable value with
            | Some name -> Set.add known name
            | None -> known
            end
        | _ -> known
      in
      let rec saturate known formulas =
        let next = List.fold formulas ~init:known ~f:derive in
        if Set.equal known next then known else saturate next formulas
      in
      let fail () =
        Error.type_error loc
          "structural predicate measures require recursive arguments and guards to be \
           determined by parameters, equalities, or full field ownership"
      in
      let rec visit known children expr =
        let known = saturate known (conjuncts expr) in
        match expr with
        | Expr.App (And, exprs, _) ->
            Rewriter.List.fold_left exprs ~init:children ~f:(visit known)
        | Expr.Binder (Exists, _, _, body, _) -> visit known children body
        | Expr.App (Ite, [ test; yes; no ], _) ->
            if not (determined known test) then fail ();
            let* children = visit known children yes in
            visit known children no
        | Expr.App (Impl, [ test; body ], _) ->
            if not (determined known test) then fail ();
            visit known children body
        | Expr.Binder (Forall, _, _, _, _) ->
            if Type.equal (Expr.to_type expr |> Type.set_ghost false) Type.bool then
              Rewriter.return children
            else
              Error.type_error loc
                "structural descent through universally quantified resource chunks is \
                 not supported"
        | _ ->
            let+ app = application expr in
            begin match app with
            | None -> children
            | Some (child, args) ->
                if not (List.for_all args ~f:(determined known)) then fail ();
                Set.add children child
            end
      in
      let* children =
        visit (Set.empty (module QualIdent)) (Set.empty (module QualIdent)) body
      in
      Rewriter.List.fold_left (Set.to_list children) ~init:visited ~f:validate
  in
  let+ _ = validate (Set.empty (module QualIdent)) root in
  ()

(* Witnesses exposed by unfold are captured before later assignments can change the
   arguments or guards. Universally quantified resource chunks need a richer rule. *)
let expose ~loc use_desc =
  let open Rewriter.Syntax in
  let* predicate = Rewriter.find_and_reify_callable use_desc.Stmt.use_name in
  let decl = predicate.call_decl in
  let body =
    match predicate.call_def with
    | FuncDef { func_body = Some body } -> body
    | _ -> Error.type_error loc "cannot use an abstract predicate for structural descent"
  in
  if not (List.is_empty decl.call_decl_returns) then
    Error.type_error loc
      "structural descent through predicates with output parameters is not supported"
  else
    let subst =
      List.zip_exn decl.call_decl_formals use_desc.use_args
      |> List.fold
           ~init:(Map.empty (module QualIdent))
           ~f:(fun subst (var, arg) ->
             Map.set subst ~key:(QualIdent.from_ident var.Type.var_name) ~data:arg)
    in
    let body = Expr.alpha_renaming body subst in
    let rec bind_existentials bindings expr =
      match expr with
      | Expr.Binder (Forall, _, _, _, _) -> Rewriter.return bindings
      | Expr.Binder (Exists, vars, _, body, _) ->
          let* bindings =
            Rewriter.List.fold_left vars ~init:bindings ~f:(fun bindings var ->
                let existing =
                  List.find use_desc.use_witnesses_or_binds ~f:(fun (_, witness) ->
                      String.equal
                        (Ident.name (Expr.to_ident witness))
                        (Ident.name var.Type.var_name))
                in
                let+ local =
                  match existing with
                  | Some (ident, _) ->
                      let+ local =
                        Rewriter.find_and_reify_var (QualIdent.from_ident ident)
                      in
                      local.var_decl
                  | None -> fresh_local ~loc "$induction_witness" var.var_type
                in
                (var, local) :: bindings)
          in
          bind_existentials bindings body
      | Expr.App (_, args, _) ->
          Rewriter.List.fold_left args ~init:bindings ~f:bind_existentials
      | Expr.Binder (_, _, _, _, _) -> Rewriter.return bindings
    in
    let* bindings = bind_existentials [] body in
    let witness_subst =
      List.fold bindings
        ~init:(Map.empty (module QualIdent))
        ~f:(fun subst (var, local) ->
          Map.set subst
            ~key:(QualIdent.from_ident var.Type.var_name)
            ~data:(Expr.from_var_decl local))
    in
    let body = Expr.supply_witnesses witness_subst body in
    let new_bindings =
      List.filter_map bindings ~f:(fun (var, local) ->
          if
            List.exists use_desc.use_witnesses_or_binds ~f:(fun (ident, _) ->
                Ident.equal ident local.Type.var_name)
          then None
          else Some (local.var_name, Expr.from_var_decl var))
    in
    let use_desc =
      {
        use_desc with
        use_witnesses_or_binds = use_desc.use_witnesses_or_binds @ new_bindings;
      }
    in
    let rec children guard expr =
      match expr with
      | Expr.App (And, args, _) ->
          let+ children = Rewriter.List.map args ~f:(children guard) in
          List.concat children
      | Expr.App (Ite, [ test; yes; no ], _) ->
          let* yes = children (Expr.mk_and ~loc [ guard; test ]) yes in
          let+ no = children (Expr.mk_and ~loc [ guard; Expr.mk_not ~loc test ]) no in
          yes @ no
      | Expr.App (Impl, [ test; body ], _) ->
          children (Expr.mk_and ~loc [ guard; test ]) body
      | Expr.Binder (Exists, _, _, body, _) -> children guard body
      | Expr.Binder (Forall, _, _, body, _) ->
          let+ nested = children guard body in
          if List.is_empty nested then []
          else
            Error.type_error loc
              "structural descent through universally quantified predicate chunks is not \
               supported"
      | _ ->
          let* app = application expr in
          begin match app with
          | None -> Rewriter.return []
          | Some (predicate, args) ->
              let+ callable = Rewriter.find_and_reify_callable predicate in
              if callable.call_decl.call_decl_is_inline then []
              else [ { predicate; args; guard; strict = true } ]
          end
    in
    let+ children = children (Expr.mk_bool ~loc true) body in
    (use_desc, children)

let rewrite_body ~same_scc ~measure_of call_decl spec body =
  let open Rewriter.Syntax in
  let* () = check_precondition call_decl spec in
  let loc = call_decl.Callable.call_decl_loc in
  let* caller = Rewriter.current_scope_id in
  let* app = application spec.Stmt.spec_form in
  let predicate, args = Option.value_exn app in
  let* () = validate_predicate ~loc:(Expr.to_loc spec.spec_form) predicate in
  let* entry_stmts, root =
    capture ~loc { predicate; args; guard = Expr.mk_bool ~loc true; strict = false }
  in
  let rec rewrite occurrences stmt =
    let loc = stmt.Stmt.stmt_loc in
    match stmt.stmt_desc with
    | Block block ->
        let+ occurrences, stmts =
          Rewriter.List.fold_left block.block_body ~init:(occurrences, [])
            ~f:(fun (occurrences, stmts) stmt ->
              let+ stmt, occurrences = rewrite occurrences stmt in
              (occurrences, stmt :: stmts))
        in
        let stmts = List.rev stmts in
        ({ stmt with stmt_desc = Block { block with block_body = stmts } }, occurrences)
    | Cond cond ->
        let* yes, yes_occurrences = rewrite occurrences cond.cond_then in
        let+ no, no_occurrences = rewrite occurrences cond.cond_else in
        let occurrences =
          List.filter yes_occurrences ~f:(fun yes ->
              List.exists no_occurrences ~f:(fun no ->
                  Expr.alpha_equal yes.guard no.guard))
        in
        ( { stmt with stmt_desc = Cond { cond with cond_then = yes; cond_else = no } },
          occurrences )
    | Basic (Use use_desc) when Poly.(use_desc.use_kind = Unfold) ->
        let* name = Rewriter.resolve use_desc.use_name in
        if
          not
            (List.exists occurrences ~f:(fun occurrence ->
                 QualIdent.equal occurrence.predicate name))
        then Rewriter.return (stmt, occurrences)
        else
          let* snapshots =
            Rewriter.List.map use_desc.use_args ~f:(snapshot ~loc "$induction_unfold_arg")
          in
          let args = List.map snapshots ~f:snd in
          let* parent_stmt, parent_guard =
            snapshot ~loc "$induction_parent"
              (Expr.mk_or ~loc (List.map occurrences ~f:(matches ~loc name args)))
          in
          let* use_desc, children = expose ~loc { use_desc with use_args = args } in
          let* remaining =
            Rewriter.List.map occurrences ~f:(fun occurrence ->
                let+ stmt, guard =
                  snapshot ~loc "$induction_remaining"
                    (Expr.mk_and ~loc
                       [
                         occurrence.guard;
                         Expr.mk_not ~loc (matches ~loc name args occurrence);
                       ])
                in
                (stmt, { occurrence with guard }))
          in
          let+ children =
            Rewriter.List.map children ~f:(fun child ->
                capture ~loc
                  { child with guard = Expr.mk_and ~loc [ parent_guard; child.guard ] })
          in
          let stmts =
            List.map snapshots ~f:fst @ [ parent_stmt ] @ List.map remaining ~f:fst
            @ [ { stmt with stmt_desc = Basic (Use use_desc) } ]
            @ List.concat_map children ~f:fst
          in
          ( Stmt.mk_block_stmt ~loc stmts,
            List.map remaining ~f:snd @ List.map children ~f:snd )
    | Basic (Call call) ->
        let* callee_name = Rewriter.resolve call.call_name in
        let* callee = Rewriter.find_and_reify_callable callee_name in
        let* checks =
          if not (same_scc caller callee_name) then Rewriter.return []
          else
            match measure_of callee.call_decl with
            | None -> Rewriter.return []
            | Some measure ->
                let subst =
                  List.zip_exn callee.call_decl.call_decl_formals call.call_args
                  |> List.fold
                       ~init:(Map.empty (module QualIdent))
                       ~f:(fun subst (var, arg) ->
                         Map.set subst
                           ~key:(QualIdent.from_ident var.Type.var_name)
                           ~data:arg)
                in
                let* app =
                  application (Expr.alpha_renaming measure.Stmt.spec_form subst)
                in
                begin match app with
                | None -> Rewriter.return []
                | Some (predicate, args) ->
                    Rewriter.return
                      [
                        Stmt.mk_assert_expr ~loc ~spec_error:spec.Stmt.spec_error
                          ~cmnt:
                            "[EXT] DecreasesExt: recursive call must use an unfolded \
                             descendant"
                          (progress ~loc predicate args occurrences);
                      ]
                end
        in
        Rewriter.return (Stmt.mk_block_stmt ~loc (checks @ [ stmt ]), [])
    | StmtExt tag ->
        let* ext_hooks = Rewriter.current_ext_hooks in
        let+ tag =
          ext_hooks.stmt_ext_rewrite ~f:Rewriter.return
            ~c:(fun nested ->
              let+ nested, _ = rewrite occurrences nested in
              nested)
            tag
        in
        ({ stmt with stmt_desc = StmtExt tag }, [])
    | Basic (Use _ | Spec ((Inhale | Exhale), _) | AUAction _ | BasicStmtExt _) | Loop _
      ->
        Rewriter.return (stmt, [])
    | Basic _ -> Rewriter.return (stmt, occurrences)
  in
  let+ body, _ = rewrite [ root ] body in
  (* At the body's location: its end is where the callable returns. *)
  Stmt.mk_block_stmt ~loc:body.stmt_loc (entry_stmts @ [ body ])
