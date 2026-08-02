(** Builds a dependency/call graph over a module's top-level symbols. Shared,
    backend-agnostic core of what [Dependencies.root_dependencies] (lib/backend/) does,
    minus that module's own auto-lemma-edge bookkeeping (a module-instantiation/backend
    concern) -- lifted here so front-end rewrite passes (e.g. the `decreases` extension's
    strongly-connected-component analysis) can reuse it without depending on lib/backend. *)

open Base
open AstDef
open Util

module Graph = Graph.Make (QualIdent)

(** Computes the dependency graph from all symbols explicitly represented in [mdef]:
    one vertex per top-level type/var/callable, with an edge to every other symbol it
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
      let deps = Option.map type_def.type_def_expr ~f:Type.symbols |> Option.value ~default:empty in
      Graph.add_edges g qid deps
    | VarDef var_def ->
      let+ qid = Rewriter.resolve (Symbol.to_name sym |> QualIdent.from_ident) in
      let deps = Option.map var_def.var_init ~f:Expr.symbols |> Option.value ~default:empty in
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
      Rewriter.List.fold_left mdef.mod_def ~f:(fun g -> function
          | SymbolDef s -> analyze_symbol g s
          | _ -> Rewriter.return g)
        ~init:g
    in
    let+ _ = Rewriter.exit_module mdef in
    g
  in
  let _, g = Rewriter.eval ~update:false (analyze_module Graph.empty mdef) tbl in
  g
