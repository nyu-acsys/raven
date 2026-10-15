(** Symbol dependencies for backend ordering and body calls for termination analysis. *)

open Base
open AstDef
open Util
module Graph = Graph.Make (QualIdent)

(** Computes the dependency graph from all symbols explicitly represented in [mdef]: one
    vertex per top-level type/var/callable, with an edge to every other symbol it
    references ([Type.symbols]/[Expr.symbols]/[Stmt.symbols] via [Callable.symbols]).
    Assumes [tbl] is the symbol table for the same [mdef]. *)
let build (tbl : SymbolTbl.t) (mdef : Module.t) : Graph.t =
  let empty = Set.empty (module QualIdent) in
  let open Module in
  let open Rewriter.Syntax in
  let rec analyze_symbol (g : Graph.t) sym =
    match sym with
    | ModDef mod_def -> analyze_module g mod_def
    | TypeDef type_def ->
        let+ qid = Rewriter.resolve (Symbol.to_name sym |> QualIdent.from_ident) in
        let deps =
          Option.map type_def.type_def_expr ~f:Type.symbols |> Option.value ~default:empty
        in
        Graph.add_edges g qid deps
    | VarDef var_def ->
        let+ qid = Rewriter.resolve (Symbol.to_name sym |> QualIdent.from_ident) in
        let deps =
          Option.map var_def.var_init ~f:Expr.symbols |> Option.value ~default:empty
        in
        let deps = Set.union deps (Type.symbols var_def.var_decl.var_type) in
        Graph.add_edges g qid deps
    | CallDef call_def ->
        let+ qid = Rewriter.resolve (Symbol.to_name sym |> QualIdent.from_ident) in
        let deps = Callable.symbols call_def in
        Graph.add_edges g qid deps
    | _ -> Rewriter.return g
  and analyze_module g mdef =
    let* _ = Rewriter.enter_module mdef in
    let* g =
      Rewriter.List.fold_left mdef.mod_def
        ~f:(fun g -> function
          | SymbolDef s -> analyze_symbol g s | _ -> Rewriter.return g)
        ~init:g
    in
    let+ _ = Rewriter.exit_module mdef in
    g
  in
  let _, g = Rewriter.eval ~update:false (analyze_module Graph.empty mdef) tbl in
  g

(** Calls made by callable bodies, excluding references in types and contracts and
    atomic-update predicate names. Used for termination analysis. *)
let termination_calls ~ext_hooks (tbl : SymbolTbl.t) (mdef : Module.t) : Graph.t =
  let open Rewriter.Syntax in
  let rec expr_calls bound calls = function
    | Expr.App (constr, args, _) ->
        let calls =
          match constr with
          | Var name when not (Set.mem bound name) -> Set.add calls name
          | _ -> calls
        in
        List.fold args ~init:calls ~f:(expr_calls bound)
    | Expr.Binder (_, vars, _, body, _) ->
        let bound =
          List.fold vars ~init:bound ~f:(fun bound var ->
              Set.add bound (QualIdent.from_ident var.Type.var_name))
        in
        expr_calls bound calls body
  in
  let analyze_callable callable =
    let decl = callable.Callable.call_decl in
    let bound =
      decl.call_decl_formals @ decl.call_decl_returns @ decl.call_decl_locals
      |> List.map ~f:(fun var -> QualIdent.from_ident var.Type.var_name)
      |> Set.of_list (module QualIdent)
    in
    (* A ref, as [Rewriter.Stmt.rewrite_expressions_top] is fixed at unit user state. *)
    let calls = ref (Set.empty (module QualIdent)) in
    let scan_expr expr =
      calls := expr_calls bound !calls expr;
      Rewriter.return expr
    in
    let rec scan_stmt stmt =
      let* () =
        match stmt.Stmt.stmt_desc with
        | Basic (Call call) ->
            calls := Set.add !calls call.call_name;
            Rewriter.return ()
        | Basic (Fpu fpu) ->
            let+ _ = scan_expr fpu.fpu_ref in
            ()
        | Basic (AUAction action) ->
            let args =
              match action.auaction_kind with
              | BindAU _ -> []
              | OpenAU action -> action.token :: action.proc_args
              | AbortAU action -> action.token :: action.proc_args
              | CommitAU action -> (action.token :: action.proc_args) @ action.proc_rets
            in
            Rewriter.List.iter args ~f:(fun expr ->
                let+ _ = scan_expr expr in
                ())
        | _ -> Rewriter.return ()
      in
      Rewriter.Stmt.rewrite_expressions_top ~f:scan_expr ~c:scan_stmt stmt
    in
    let* () =
      match (decl.call_decl_kind, callable.call_def) with
      | Func, FuncDef { func_body = Some body } ->
          let+ _ = scan_expr body in
          ()
      | (Proc | Lemma), ProcDef { proc_body = Some body } ->
          let+ _ = scan_stmt body in
          ()
      | _ -> Rewriter.return ()
    in
    let+ callees =
      Rewriter.List.map (Set.to_list !calls) ~f:(fun name ->
          let* name, symbol = Rewriter.resolve_and_find name in
          let+ symbol = Rewriter.Symbol.reify symbol in
          match symbol with
          | Module.CallDef { call_decl = { call_decl_kind = Func | Proc | Lemma; _ }; _ }
            ->
              Some name
          | _ -> None)
    in
    List.filter_opt callees |> Set.of_list (module QualIdent)
  in
  let rec analyze_module graph mdef =
    let* _ = Rewriter.enter_module mdef in
    let* graph =
      Rewriter.List.fold_left mdef.Module.mod_def ~init:graph ~f:(fun graph -> function
        | Module.SymbolDef (ModDef nested) -> analyze_module graph nested
        | Module.SymbolDef (CallDef callable) ->
            let* _ = Rewriter.enter_callable callable in
            let* name = Rewriter.current_scope_id in
            let* callees = analyze_callable callable in
            let+ _ = Rewriter.exit_callable callable in
            Graph.add_edges graph name callees
        | _ -> Rewriter.return graph)
    in
    let+ _ = Rewriter.exit_module mdef in
    graph
  in
  let _, graph =
    Rewriter.eval ~ext_hooks ~update:false (analyze_module Graph.empty mdef) tbl
  in
  graph

(** Edges from each lemma in [mdef] to the callables its body calls. Must run before calls
    are elaborated into their callees' contracts, which erases these edges from the AST
    although a lemma's proof still depends on its callees being proved first. *)
let lemma_calls (tbl : SymbolTbl.t) (mdef : Module.t) : Graph.t =
  let open Module in
  let open Rewriter.Syntax in
  let rec stmt_calls acc (s : Stmt.t) =
    match s.stmt_desc with
    | Block b -> List.fold b.block_body ~init:acc ~f:stmt_calls
    | Basic (Call call_desc) -> call_desc.call_name :: acc
    | Basic _ | StmtExt _ -> acc
    | Loop l -> stmt_calls (stmt_calls acc l.loop_prebody) l.loop_postbody
    | Cond c -> stmt_calls (stmt_calls acc c.cond_then) c.cond_else
  in
  let rec analyze_symbol (g : Graph.t) sym =
    match sym with
    | ModDef mod_def -> analyze_module g mod_def
    | CallDef
        {
          call_decl = { call_decl_kind = Lemma; _ };
          call_def = ProcDef { proc_body = Some body };
        } ->
        let* qid = Rewriter.resolve (Symbol.to_name sym |> QualIdent.from_ident) in
        let+ callees = Rewriter.List.map (stmt_calls [] body) ~f:Rewriter.resolve in
        Graph.add_edges g qid (Set.of_list (module QualIdent) callees)
    | _ -> Rewriter.return g
  and analyze_module g mdef =
    let* _ = Rewriter.enter_module mdef in
    let* g =
      Rewriter.List.fold_left mdef.mod_def ~init:g ~f:(fun g -> function
        | SymbolDef s -> analyze_symbol g s
        | _ -> Rewriter.return g)
    in
    let+ _ = Rewriter.exit_module mdef in
    g
  in
  let _, g = Rewriter.eval ~update:false (analyze_module Graph.empty mdef) tbl in
  g
