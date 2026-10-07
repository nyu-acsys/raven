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
          | _ ->
              Error.internal_error stmt.stmt_loc
                (Printf.sprintf "Internal error: statement %s reached the backend with an unexpected spec kind (this indicates a bug in the verifier, not a problem with your proof)" (Stmt.to_string stmt)))
      | _ ->
          Error.internal_error stmt.stmt_loc
            (Printf.sprintf "Internal error: statement %s reached the backend in an unexpected form (this indicates a bug in the verifier, not a problem with your proof)" (Stmt.to_string stmt)))
  | _ ->
      Error.internal_error stmt.stmt_loc
        (Printf.sprintf "Internal error: statement %s reached the backend in an unexpected form (this indicates a bug in the verifier, not a problem with your proof)" (Stmt.to_string stmt))

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

        (* The func's contract is checked and assumed by its companion auto lemma
           (see [Rewrites.rewrite_add_func_contract_lemmas]), not here. *)
        assume_expr spec_expr)
  | ProcDef proc_def -> (
      match proc_def.proc_body with
      | Some stmt when not (is_free callable.call_decl.call_decl_status) ->
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

          pop
      | _ ->
        Logs.debug (fun m -> m "Skipping %b" (is_free callable.call_decl.call_decl_status));
        State.return ())

let is_auto_lemma (callable : Ast.Callable.t) =
  match callable with
  | { call_def = ProcDef _; call_decl = { call_decl_kind = Lemma; call_decl_is_auto = true; _ } } ->
      true
  | _ -> false

(** Assumes the contract of the auto lemma [callable]. *)
let assume_auto_lemma (fully_qual_name : qual_ident) (callable : Ast.Callable.t) : unit t =
  let open State.Syntax in
  let call_decl = callable.call_decl in
  let* _ =
    write_comment
      (Stdlib.Format.asprintf "Auto lemma: %a" QualIdent.pr fully_qual_name)
  in
  let under_precond postcond =
    match call_decl.call_decl_precond with
    | [] -> postcond
    | precond ->
        Expr.mk_impl
          (Expr.mk_and (List.map precond ~f:(fun spec -> spec.spec_form)))
          postcond
  in
  let quantified ?trigs postconds =
    Expr.mk_binder ~loc:call_decl.call_decl_loc ?trigs Forall call_decl.call_decl_formals
      (under_precond (Expr.mk_and (List.map postconds ~f:(fun spec -> spec.Stmt.spec_form))))
  in
  (* A postcondition with triggers is quantified on its own, with its triggers. *)
  let triggered, untriggered =
    List.partition_tf call_decl.call_decl_postcond ~f:(fun spec ->
        not (List.is_empty spec.Stmt.spec_trigs))
  in
  let axioms =
    (if List.is_empty untriggered then [] else [ quantified untriggered ])
    @ List.map triggered ~f:(fun spec -> quantified ~trigs:spec.spec_trigs [ spec ])
  in
  State.List.iter axioms ~f:assume_expr

(** Whether the function [qual_name] is emitted as a macro (`define-fun`) rather than as
    a declared function with a defining axiom: it is declared `inline`. The marker is a
    hint, ignored for a function that is recursive. *)
let is_macro (g : Dependencies.Graph.t) (qual_name : qual_ident) (callable : Ast.Callable.t) :
    bool =
  match callable with
  | {
   call_def = FuncDef { func_body = Some _ };
   call_decl = { call_decl_kind = Func; call_decl_is_inline = true; call_decl_returns = [ _ ]; _ };
  } ->
      not
        (Set.mem
           (Dependencies.Graph.reachable g (Dependencies.Graph.succs g qual_name))
           qual_name)
  | _ -> false

(** Declares and checks a single SCC ([dep], as returned by [Dependencies.analyze]) at
    whatever scope is currently open -- the caller ([check_members]) is responsible for
    getting that scope right first. Function symbols get their [declare-fun] before anything
    in the group is checked (so mutually-recursive references resolve), likewise datatypes
    before their constructors/destructors are used; both match [check_member]'s own needs. *)
let declare_and_check_dep (tbl : SymbolTbl.t) (g : Dependencies.Graph.t) (dep : QualIdent.t list) : unit t =
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
      (* A constructor/destructor is declared as part of its own datatype's
         `declare-datatypes`, above in [data_types] -- see [Dependencies.analyze]'s
         [ConstrDef]/[DestrDef] cases, which point a reference to one at that
         datatype so it's discovered even when nothing else names the type. Nothing
         further to do for the constructor/destructor symbol itself here. *)
      | ConstrDef _ | DestrDef _ -> Rewriter.return ()
      | _ ->
        Error.unsupported_error Loc.dummy
          ("Unsupported symbol: " ^ Symbol.to_string symbol)
  in

  let dep_sym =
    List.map dep ~f:(fun qual_name ->
      let tbl1 = SymbolTbl.goto qual_name tbl in
      let _, symbol = Rewriter.eval ~update:false (Rewriter.find_and_reify qual_name) tbl1 in
      (qual_name, symbol))
  in

  let macros =
    List.filter_map dep_sym ~f:(function
      | qual_name, Module.CallDef callable when is_macro g qual_name callable ->
          Some (qual_name, callable)
      | _ -> None)
  in
  let is_macro_name qual_name =
    List.exists macros ~f:(fun (q, _) -> QualIdent.equal q qual_name)
  in

  let dep_sym_fn = List.filter dep_sym ~f:(function
    | qual_name, Module.CallDef { call_def = FuncDef _; _ } -> not (is_macro_name qual_name)
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

  (* Macros of the same component are defined after those their bodies use, which is
     possible as none of them is recursive. *)
  let rec define_macros defined pending =
    match
      List.partition_tf pending ~f:(fun (qual_name, _) ->
          Set.for_all (Dependencies.Graph.succs g qual_name) ~f:(fun q ->
              Set.mem defined q || not (is_macro_name q)))
    with
    | [], [] -> Rewriter.return ()
    | [], _ :: _ -> Error.internal_error Loc.dummy "Checker: cyclic macro definitions"
    | ready, pending ->
        let* _ =
          State.List.iter ready ~f:(fun (qual_name, (callable : Ast.Callable.t)) ->
              match (callable.call_def, callable.call_decl.call_decl_returns) with
              | FuncDef { func_body = Some body }, [ ret ] ->
                  write
                    (SmtLibAST.mk_define_fun ~loc:callable.call_decl.call_decl_loc qual_name
                       (List.map callable.call_decl.call_decl_formals ~f:(fun arg ->
                            (QualIdent.from_ident arg.var_name, arg.var_type)))
                       ret.var_type body)
              | _ -> Error.internal_error Loc.dummy "Checker: macro without body")
        in
        define_macros
          (List.fold ready ~init:defined ~f:(fun acc (q, _) -> Set.add acc q))
          pending
  in
  let* _ = define_macros (Set.empty (module QualIdent)) macros in

  (* An auto lemma is assumed only once every member of the SCC that its proof depends on
     has been checked, so that no proof can rely on its own conclusion. *)
  let members = Set.of_list (module QualIdent) dep in
  let proof_deps qid =
    let rec reach seen = function
      | [] -> seen
      | v :: todo ->
          let next =
            Set.filter (Dependencies.Graph.succs g v) ~f:(fun w ->
              Set.mem members w && not (Set.mem seen w))
          in
          reach (Set.union seen next) (Set.to_list next @ todo)
    in
    reach (Set.singleton (module QualIdent) qid) [ qid ]
  in
  let auto_lemmas =
    List.filter_map dep_sym ~f:(function
      | qual_name, Module.CallDef callable when is_auto_lemma callable ->
          Some (qual_name, callable, proof_deps qual_name)
      | _ -> None)
  in
  let assume_ready checked pending =
    let ready, pending =
      List.partition_tf pending ~f:(fun (_, _, deps) -> Set.is_subset deps ~of_:checked)
    in
    let+ _ =
      State.List.iter ready ~f:(fun (qual_name, callable, _) ->
          assume_auto_lemma qual_name callable)
    in
    pending
  in
  let+ _ =
    State.List.fold_left dep_sym ~init:(Set.empty (module QualIdent), auto_lemmas)
      ~f:(fun (checked, pending) (qual_name, sym) ->
        let* _ =
          (* A macro's definition already says everything its axiom would. *)
          if is_macro_name qual_name then Rewriter.return () else check_member qual_name sym
        in
        let checked = Set.add checked qual_name in
        let+ pending = assume_ready checked pending in
        (checked, pending))
  in
  ()

(** A tree grouping the SCCs of [placed] by the module-path scope
    [Dependencies.compute_placements] assigned each one, mirroring the nesting those paths
    describe: [own_rev] holds every SCC placed at exactly this node's path (most recently
    added first -- built by prepending, like [child_order_rev], to keep construction linear
    rather than quadratic; both get reversed once, in [walk], on the way out), [children] the
    subtrees for paths one component longer. Two SCCs placed at the same path need not be
    adjacent in [placed]'s (whole-program) topological order -- something with a different,
    unrelated placement can easily fall between them -- so grouping by path has to happen
    explicitly like this rather than by diffing each SCC's path against the one before it. *)
module PathTree = struct
  type t = {
    mutable own_rev : QualIdent.t list list;
    children : (Ident.t, t) Hashtbl.t;
    mutable child_order_rev : Ident.t list;
  }

  let create () : t = { own_rev = []; children = Hashtbl.create (module Ident); child_order_rev = [] }

  let rec scope (root : t) (path : Ident.t list) : t =
    match path with
    | [] -> root
    | id :: rest ->
      let child = match Hashtbl.find root.children id with
        | Some child -> child
        | None ->
          let child = create () in
          Hashtbl.set root.children ~key:id ~data:child;
          root.child_order_rev <- id :: root.child_order_rev;
          child
      in
      scope child rest

  let of_placed (placed : (Ident.t list * QualIdent.t list) list) : t =
    let root = create () in
    List.iter placed ~f:(fun (path, dep) ->
      let node = scope root path in
      node.own_rev <- dep :: node.own_rev);
    root
end

(** Walks the [PathTree] built from [placed], declaring/checking each node's own SCCs (in
    their relative dependency order -- a subsequence of a topological order is itself a valid
    topological order) before descending into its children, each under its own nested
    [push]/[pop]: nothing a node's own SCCs need can live in one of its children (a symbol's
    placement is always an ancestor of everywhere it's used, never a sibling or a descendant
    -- see [Dependencies.compute_placements]), so it's always safe to declare a node's own
    members first and only then open its children's scopes. *)
let check_members (placed : (Ident.t list * QualIdent.t list) list) (g : Dependencies.Graph.t) tbl =
  Logs.debug(fun m -> m "Checker.check_members: placed= %a"
      (Util.Print.pr_list_nl (fun ppf (path, dep) ->
           Stdlib.Format.fprintf ppf "@[%a@] : %a" (Util.Print.pr_list_comma Ident.pr) path (Util.Print.pr_list_comma QualIdent.pr) dep))
      placed );
  let open Rewriter.Syntax in
  let rec walk (node : PathTree.t) : unit t =
    let* _ = State.List.iter (List.rev node.own_rev) ~f:(declare_and_check_dep tbl g) in
    State.List.iter (List.rev node.child_order_rev) ~f:(fun id ->
      let child = Hashtbl.find_exn node.children id in
      let* _ = push in
      let* _ = write_comment (Stdlib.Format.asprintf "Checking members in %a" Ident.pr id) in
      let* _ = walk child in
      pop)
  in
  walk (PathTree.of_placed placed)

let check_module (module_defs : Ast.Module.t list) (lemma_calls : Dependencies.Graph.t)
    (tbl : SymbolTbl.t) (smt_env : smt_env) : smt_env =
  let dependencies, deps_graph, auto_dependencies =
    Dependencies.analyze tbl module_defs lemma_calls smt_env.auto_dependencies
  in

  Logs.debug (fun m ->
      m "Dependencies: %a"
        (Util.Print.pr_list_sep " ]]\n" (fun ppf (path, dep) ->
             Stdlib.Format.fprintf ppf "@[%a@] : %a" (Util.Print.pr_list_comma Ident.pr) path (Util.Print.pr_list_comma QualIdent.pr) dep))
        dependencies);

  let smt_env = { smt_env with auto_dependencies } in

  let smt_env, _ =
    State.eval
      (check_members dependencies deps_graph tbl) smt_env
  in
  smt_env
