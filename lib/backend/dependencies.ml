open Base
open Util
open Ast


module Graph = Ast.CallGraph.Graph

(** Compute partial dependency graph from all symbols that are explicitely represented in the AST.
    The base graph [g] is [Ast.CallGraph.build] (shared with front-end rewrite passes, e.g. the
    `decreases` extension's SCC analysis); this walk layers on top of it the backend-only
    auto-lemma edges (an [ag] accumulator: for every [call_decl_is_auto] callable, an edge from
    each same-path dependency back to it), which is module-instantiation/backend bookkeeping with
    no front-end use. *)
let root_dependencies (tbl: SymbolTbl.t) (mdef: Module.t) (ag: Graph.t) =
  let open Module in
  let open Rewriter.Syntax in
  let rec analyze_auto_deps (ag: Graph.t) sym =
    match sym with
    | ModDef mod_def -> analyze_auto_deps_module ag mod_def
    | CallDef call_def when (Callable.to_decl call_def).call_decl_is_auto ->
      let+ qid = Rewriter.resolve (Symbol.to_name sym |> QualIdent.from_ident) in
      let deps = Callable.symbols call_def in
      Logs.debug (fun m -> m "Dependencies.root_dependencies: Adding dependencies of callable %a: %a" QualIdent.pr qid (Print.pr_list_comma QualIdent.pr) (Set.elements deps));
      Set.fold deps ~f:(fun ag dep_qid ->
          if List.equal Ident.(=) QualIdent.(path qid) QualIdent.(path dep_qid)
          then
            let _ = Logs.debug (fun m -> m "Dependencies.root_dependencies: adding auto dependency %a -> %a" QualIdent.pr dep_qid QualIdent.pr qid) in
            Graph.add_edge ag dep_qid qid else ag) ~init:ag
    | _ -> Rewriter.return ag
  and analyze_auto_deps_module ag mdef =
    let* _ = Rewriter.enter_module mdef in
    let* ag = Rewriter.List.fold_left mdef.mod_def ~f:(fun ag -> function
        | SymbolDef s -> analyze_auto_deps ag s
        | _ -> Rewriter.return ag)
        ~init:ag
    in
    let+ _ = Rewriter.exit_module mdef in
    ag
  in
  let g = Ast.CallGraph.build tbl mdef in
  let _, ag = Rewriter.eval ~update:false (analyze_auto_deps_module ag mdef) tbl in
  g, ag

(** The longest shared prefix of two module paths -- used to find the shallowest scope that
    is an ancestor of both. *)
let rec common_prefix (p1: Ident.t list) (p2: Ident.t list) : Ident.t list =
  match p1, p2 with
  | id1 :: rest1, id2 :: rest2 when Ident.(id1 = id2) -> id1 :: common_prefix rest1 rest2
  | _ -> []

(** For each SCC in [symbols] (dependency-first, as returned by [Graph.topsort]), the module
    path it should be declared at: the deepest scope common to every symbol elsewhere in
    [symbols] that references it (falling back to the SCC's own path -- the common prefix of
    its own members, for a mutually-recursive group spanning more than one module -- if
    nothing does). A symbol used from a single module keeps that module's own scope; one used
    from several is hoisted to their common ancestor, all the way up to the empty path (the
    outermost scope, never popped) if the modules that need it share no common ancestor at all.

    Computed in a single reverse (dependent-first) pass: by the time an SCC is visited, every
    symbol that could still push its placement outward (further inward is impossible, since
    dependents come later in [symbols] than what they depend on) has already been finalized,
    so its own placement can be propagated onto what it depends on. [g]/[full_g] are the
    explicit and auto-dependency edges [Graph.topsort (Graph.union g full_g)] was called on to
    produce [symbols]. *)
let compute_placements (symbols: QualIdent.t list list) (g: Graph.t) (full_g: Graph.t)
  : (Ident.t list * QualIdent.t list) list =
  let scc_index = Hashtbl.create (module QualIdent) in
  List.iteri symbols ~f:(fun i scc ->
    List.iter scc ~f:(fun qid -> Hashtbl.set scc_index ~key:qid ~data:i));
  let sccs = Array.of_list symbols in
  let n = Array.length sccs in
  let placement = Array.create ~len:n None in
  for i = n - 1 downto 0 do
    let scc = sccs.(i) in
    let own_path = match scc with
      | [] -> []
      | qid :: qids -> List.fold qids ~init:(QualIdent.path qid) ~f:(fun acc qid -> common_prefix acc (QualIdent.path qid))
    in
    let my_placement = Option.value placement.(i) ~default:own_path in
    placement.(i) <- Some my_placement;
    let scc_members = Set.of_list (module QualIdent) scc in
    let deps =
      List.fold scc ~init:Graph.empty_vertex_set ~f:(fun acc qid ->
        Set.union acc (Set.union (Graph.succs g qid) (Graph.succs full_g qid)))
      |> Fn.flip Set.diff scc_members
    in
    Set.iter deps ~f:(fun dep_qid ->
      match Hashtbl.find scc_index dep_qid with
      | None -> ()
      | Some j ->
        placement.(j) <- Some (match placement.(j) with
          | None -> my_placement
          | Some existing -> common_prefix existing my_placement))
  done;
  List.mapi symbols ~f:(fun i scc -> Option.value placement.(i) ~default:[], scc)

(** Produce a topological sort of the strongly connected components in the combined
    dependency graph of every module in [mdefs], treated as siblings under an implicit root
    (this is how the library and the program being checked actually relate: two separate
    top-level symbol-table entries, not one nested inside the other), together with each
    SCC's [compute_placements] scope. [tbl] is the symbol table shared by all of [mdefs]. *)
let analyze (tbl: SymbolTbl.t) (mdefs: Module.t list) (root_auto_g: Graph.t)
  : (Ident.t list * QualIdent.t list) list * Graph.t =
  let rec inst_dependencies todos covered g auto_g root_auto_g =
    let res =
      let open Option.Syntax in
      let+ qid = Set.choose todos in
      (* let _, _, sym, sm = SymbolTbl.resolve_and_find_exn (QualIdent.to_loc qid) qid tbl in *)
      let tbl1 = SymbolTbl.goto qid tbl in
      let _, sym = Rewriter.eval ~update:false (Rewriter.find qid) tbl1 in
      let subst = Rewriter.Symbol.subst sym in
      let orig_qid = Rewriter.Symbol.orig_qid sym in
      let _, reified_sym = Rewriter.eval ~update:false (Rewriter.Symbol.reify sym) tbl in
      let deps, auto_deps = match reified_sym with
        | TypeDef type_def ->
          Logs.debug (fun m -> m "Dependencies.analyze: Analyzing dependencies of type %a" Symbol.pr reified_sym);
          Option.map type_def.type_def_expr ~f:Type.symbols |> Option.value ~default:Graph.empty_vertex_set, Graph.empty_vertex_set
        | CallDef call_def ->
          let open Callable in
          Logs.debug (fun m -> m "Dependencies.analyze: Analyzing dependencies of callable %a" Symbol.pr reified_sym);
          begin match Callable.kind call_def with
            | Func ->
              let orig_auto_deps = Graph.succs root_auto_g orig_qid in
              let auto_deps = Set.map (module QualIdent) orig_auto_deps ~f:(QualIdent.requalify subst) in
              Callable.symbols call_def, auto_deps
            | Pred | Invariant | Lemma | Proc ->
              Callable.symbols call_def, Graph.empty_vertex_set
          end
        | VarDef var_def ->
          Logs.debug (fun m -> m "Dependencies.analyze: Analyzing dependencies of variable %a" Symbol.pr reified_sym);
          let orig_auto_deps = Graph.succs root_auto_g orig_qid in
          let auto_deps = Set.map (module QualIdent) orig_auto_deps ~f:(QualIdent.requalify subst) in
          let deps = Option.map var_def.var_init ~f:Expr.symbols |> Option.value ~default:Graph.empty_vertex_set in
          let deps = Set.union deps (Type.symbols var_def.var_decl.var_type) in
          deps, auto_deps
        | ConstrDef constr_def ->
          (* A constructor is declared as part of its own datatype's
             `declare-datatypes` ([Checker.declare_and_check_dep]'s [data_types]
             extraction), not on its own -- [check_member] skips it -- so what a
             reference to it actually needs pulled in is that datatype. Without this,
             an expression that calls a constructor but never also names its type
             (e.g. via a `var` declaration, whose own declared type is scanned
             separately) would leave the datatype's declaration undiscovered. *)
          Type.symbols constr_def.constr_return_type, Graph.empty_vertex_set
        | DestrDef destr_def ->
          Type.symbols destr_def.destr_arg, Graph.empty_vertex_set
        | _ -> Graph.empty_vertex_set, Graph.empty_vertex_set
      in
      Logs.debug (fun m -> m "Dependencies.analyze: Adding dependencies of %a: %a" QualIdent.pr qid (Print.pr_list_comma QualIdent.pr) (Set.elements deps));
      let g1 = Graph.add_edges g qid deps in
      let auto_g1 = Graph.add_edges auto_g qid auto_deps in
      let covered1 = Set.add covered qid in
      let todos1 = Set.union (Set.remove todos qid) (Set.diff (Set.union auto_deps deps) covered1) in
      inst_dependencies todos1 covered1 g1 auto_g1 root_auto_g
    in
    Option.value res ~default:(g, auto_g)
  in
  let root_g, root_auto_g1 =
    List.fold mdefs ~init:(Graph.empty, root_auto_g) ~f:(fun (root_g, ag) mdef ->
      Logs.debug (fun m -> m "Dependencies.analyze: Analyzing dependencies of module %a" Ident.pr mdef.mod_decl.mod_decl_name);
      let root_g1, ag1 = root_dependencies tbl mdef ag in
      Graph.union root_g root_g1, ag1)
  in
  let roots = Graph.vertices root_g in
  let targets = Graph.targets root_g in
  Logs.debug (fun m -> m "Dependencies.analyze: combined roots/targets: %a" (Print.pr_list_comma QualIdent.pr) (Set.elements (Set.union roots targets)));
  let g, full_g = inst_dependencies (Set.union targets roots) Graph.empty_vertex_set root_g Graph.empty root_auto_g1 in
  Logs.debug (fun m -> m "Graph: %a" (Graph.pr QualIdent.pr) g);
  let rank, _ =
    List.fold_left (Graph.topsort g) ~init:(Map.empty (module QualIdent), 0)
      ~f:(fun rank_c sc ->
          List.fold sc ~init:rank_c ~f:(fun (rank, c) v -> Map.set rank ~key:v ~data:c, c+1)
        )
  in
  let scs = Graph.topsort (Graph.union g full_g) in
  let symbols = List.map scs ~f:(List.sort ~compare:(fun v1 v2 -> compare (Map.find_exn rank v1) (Map.find_exn rank v2))) in
  compute_placements symbols g full_g, root_auto_g1
