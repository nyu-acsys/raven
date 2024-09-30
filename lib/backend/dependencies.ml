open Base
open Util
open Ast


module Graph = Graph.Make (QualIdent)

(** Compute partial dependency graph from all symbols that are explicitely represented in the AST *)
let root_dependencies (tbl: SymbolTbl.t) (mdef: Module.t) (ag: Graph.t) =
  let empty = Set.empty (module QualIdent) in
  let open Module in
  let open Rewriter.Syntax in
  let rec analyze_symbol (g: Graph.t) (ag: Graph.t) sym =
    match sym with
    | ModDef mod_def -> analyze_module g ag mod_def
    | TypeDef type_def ->
      let+ qid = Rewriter.resolve (Symbol.to_loc sym) (Symbol.to_name sym |> QualIdent.from_ident) in
      let deps = Option.map type_def.type_def_expr ~f:Type.symbols |> Option.value ~default:empty in
      Graph.add_edges g qid deps, ag
    | VarDef var_def ->
      let+ qid = Rewriter.resolve (Symbol.to_loc sym) (Symbol.to_name sym |> QualIdent.from_ident) in
      let deps = Option.map var_def.var_init ~f:Expr.symbols |> Option.value ~default:empty in
      let deps = Set.union deps (Type.symbols var_def.var_decl.var_type) in
      Graph.add_edges g qid deps, ag
    | CallDef call_def -> 
      let+ qid = Rewriter.resolve (Symbol.to_loc sym) (Symbol.to_name sym |> QualIdent.from_ident) in
      let deps = Callable.symbols call_def in
      Logs.debug (fun m -> m "Dependencies.root_dependencies: Adding dependencies of callable %a: %a" QualIdent.pr qid (Print.pr_list_comma QualIdent.pr) (Set.elements deps));
      Graph.add_edges g qid deps,
      if (Callable.to_decl call_def).call_decl_is_auto
      then Set.fold deps ~f:(fun g dep_qid ->
          if List.equal Ident.(=) QualIdent.(path qid) QualIdent.(path dep_qid)
          then Graph.add_edge g dep_qid qid else g) ~init:ag
      else ag
    (*| ConstrDef cdef -> ???
      | DestrDef cdef -> ??? *)
    | _ -> Rewriter.return (g, ag)
  and analyze_module g ag mdef =
    let* _ = Rewriter.enter_module mdef in
    let* g, ag = Rewriter.List.fold_left mdef.mod_def ~f:(fun (g, ag) -> function
        | SymbolDef s -> analyze_symbol g ag s
        | _ -> Rewriter.return (g, ag))
        ~init:(g, ag)
    in
    let+ _ = Rewriter.exit_module mdef in
    g, ag
  in
  let _, (g, ag) = Rewriter.eval ~update:false (analyze_module Graph.empty ag mdef) tbl in
  g, ag

(** Produce a topological sort of the strongly connected components in the dependency graph of module [mdef]. *)
(** Assumes that [tbl] is the symbol table and [mdef] the root module of the program. *)
let analyze (tbl: SymbolTbl.t) (mdef: Module.t) (ag: Graph.t): QualIdent.t list list * Graph.t =
  let rec inst_dependencies todos covered g auto_g =
    let res =
      let open Option.Syntax in
      let+ qid = Set.choose todos in
      (* let _, _, sym, sm = SymbolTbl.resolve_and_find_exn (QualIdent.to_loc qid) qid tbl in *)
      let _, sym = Rewriter.eval ~update:false (Rewriter.find (QualIdent.to_loc qid) qid) tbl in
      let subst = Rewriter.Symbol.subst sym in
      let orig_qid = Rewriter.Symbol.orig_qid sym in
      let _, reified_sym = Rewriter.eval ~update:false (Rewriter.Symbol.reify sym) tbl in
      let deps = match reified_sym with
        | TypeDef type_def ->
          Logs.debug (fun m -> m "Dependencies.analyze: Analyzing dependencies of type %a" Symbol.pr reified_sym);
          Option.map type_def.type_def_expr ~f:Type.symbols |> Option.value ~default:Graph.empty_vertex_set
        | CallDef call_def ->
          let open Callable in
          begin match Callable.kind call_def with
            | Func ->
              let orig_auto_deps = Graph.succs auto_g orig_qid in
              let auto_deps = Set.map (module QualIdent) orig_auto_deps ~f:(QualIdent.requalify subst) in
              Set.union auto_deps (Callable.symbols call_def)                
            | Pred | Invariant | Lemma ->              
              Callable.symbols call_def
            | _ -> Graph.empty_vertex_set
          end
        | VarDef var_def ->
          Logs.debug (fun m -> m "Dependencies.analyze: Analyzing dependencies of variable %a" Symbol.pr reified_sym);
          let deps = Option.map var_def.var_init ~f:Expr.symbols |> Option.value ~default:Graph.empty_vertex_set in
          let deps = Set.union deps (Type.symbols var_def.var_decl.var_type) in
          deps
        | _ -> Graph.empty_vertex_set
      in
      Logs.info (fun m -> m "Dependencies.analyze: Adding dependencies of %a: %a" QualIdent.pr qid (Print.pr_list_comma QualIdent.pr) (Set.elements deps));
      let g1 = Graph.add_edges g qid deps in
      let covered1 = Set.add covered qid in
      let todos1 = Set.union (Set.remove todos qid) (Set.diff deps covered1) in
      inst_dependencies todos1 covered1 g1 auto_g
    in
    Option.value res ~default:g
  in
  Logs.debug (fun m -> m "Dependencies.analyze: Analyzing dependencies of module %a" Ident.pr mdef.mod_decl.mod_decl_name);
  let root_g, auto_g = root_dependencies tbl mdef ag in
  Logs.debug (fun m -> m "Dependencies.analyze: Root Dependencies done for module %a" Ident.pr mdef.mod_decl.mod_decl_name);
  Logs.debug (fun m -> m "Dependencies.analyze: Root Dependencies for module %a: %a" Ident.pr mdef.mod_decl.mod_decl_name (Print.pr_list_comma QualIdent.pr) (Set.elements (Set.union (Graph.targets root_g) (Graph.vertices root_g))));
  let roots = Graph.vertices root_g in
  let targets = Graph.targets root_g in
  let g = inst_dependencies (Set.diff targets roots) roots root_g auto_g in
  Graph.topsort g, auto_g
