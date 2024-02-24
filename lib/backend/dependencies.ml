open Base
open Util
open Ast


module Graph = Graph.Make (QualIdent)

(** Compute partial dependency graph from all symbols that are explicitely represented in the AST *)
let root_dependencies (tbl: SymbolTbl.t) (mdef: Module.t) =
  let empty = Set.empty (module QualIdent) in
  let open Module in
  let open Rewriter.Syntax in
  let rec analyze_symbol (g: Graph.t) sym =
    match sym with
    | ModDef mod_def -> analyze_module g mod_def
    | TypeDef type_def ->
      let+ qid = Rewriter.resolve (Symbol.to_loc sym) (Symbol.to_name sym |> QualIdent.from_ident) in
      let deps = Option.map type_def.type_def_expr ~f:Type.symbols |> Option.value ~default:empty in
      Graph.add_edges g qid deps
    | VarDef var_def ->
      let+ qid = Rewriter.resolve (Symbol.to_loc sym) (Symbol.to_name sym |> QualIdent.from_ident) in
      let deps = Option.map var_def.var_init ~f:Expr.symbols |> Option.value ~default:empty in
      Graph.add_edges g qid deps
    | CallDef call_def -> 
      let+ qid = Rewriter.resolve (Symbol.to_loc sym) (Symbol.to_name sym |> QualIdent.from_ident) in
      let deps = Callable.symbols call_def in
      Graph.add_edges g qid deps
    (*| ConstrDef cdef -> ???
      | DestrDef cdef -> ??? *)
    | _ -> Rewriter.return g
  and analyze_module g mdef =
    let* _ = Rewriter.enter_module mdef in
    let* g = Rewriter.List.fold_left mdef.mod_def ~f:(fun g -> function
        | SymbolDef s -> analyze_symbol g s
        | _ -> Rewriter.return g)
        ~init:g
    in
    let+ _ = Rewriter.exit_module mdef in
    g
  in
  let _, g = Rewriter.eval ~update:false (analyze_module Graph.empty mdef) tbl in
  g

(** Produce a topological sort of the strongly connected components in the dependency graph of module [mdef]. *)
(** Assumes that [tbl] is the symbol table and [mdef] the root module of the program. *)
let analyze (tbl: SymbolTbl.t) (mdef: Module.t): QualIdent.t list list =
  let rec inst_dependencies todos covered g =
    let res =
      let open Option.Syntax in
      let+ qid = Set.choose todos in
      let _, _, sym, sm = SymbolTbl.resolve_and_find_exn (QualIdent.to_loc qid) qid tbl in
      let deps = match sym with
        | TypeDef type_def ->
          Option.map type_def.type_def_expr ~f:Type.symbols |> Option.value ~default:Graph.empty_vertex_set
        | CallDef call_def ->
          let open Callable in
          begin match Callable.kind call_def with
          | Func | Pred | Invariant ->
            Callable.symbols call_def
          | _ -> Graph.empty_vertex_set
          end
        | _ -> Graph.empty_vertex_set
      in
      let g1 = Graph.add_edges g qid deps in
      let covered1 = Set.add covered qid in
      let todos1 = Set.union (Set.remove todos qid) (Set.diff deps covered1) in
      inst_dependencies todos1 covered1 g1
    in
    Option.value res ~default:g
  in
  Logs.debug (fun m -> m "Dependencies.analyze: Analyzing dependencies of module %a" Ident.pr mdef.mod_decl.mod_decl_name);
  let root_g = root_dependencies tbl mdef in
  Logs.debug (fun m -> m "Dependencies.analyze: Root Dependencies done for module %a" Ident.pr mdef.mod_decl.mod_decl_name);
  let roots = Graph.vertices root_g in
  let targets = Graph.targets root_g in
  let g = inst_dependencies (Set.diff targets roots) roots root_g in
  Graph.topsort g
