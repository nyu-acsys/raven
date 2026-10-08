open Base
open Ast
open Util

type supported_extensions = DefaultExt | ErisExt | ProphecyExt

let ext_map = [ ("default", ProphecyExt); ("eris", ErisExt) ]

module DefaultExtInstance = DefaultExt.DefaultExt

(* DecreasesExt is folded in unconditionally, rather than being one more
   mutually-exclusive `--extension` choice: termination checking via `decreases` clauses
   is orthogonal to which resource-algebra extension is active, so it must be available
   under `default` and `eris` alike. *)
module DecreasesExtInstance = DecreasesExt.DecreasesExt (DefaultExtInstance)

(* AssertWithExt (`assert e with { ... }`) is folded in unconditionally too, for the
   same reason as DecreasesExt above: it's a core-language proof construct, orthogonal
   to which resource-algebra extension is active. *)
module AssertWithExtInstance = AssertWithExt.AssertWithExt (DecreasesExtInstance)

(* MatchExt (ADT recognizer test / `match`) is folded in unconditionally too, for the
   same reason as DecreasesExt/AssertWithExt above: ADT ergonomics is orthogonal to
   which resource-algebra extension is active. *)
module MatchExtInstance = MatchExt.MatchExt (AssertWithExtInstance)

(* ArrayExt (indexing syntax for `Library.Array`) is folded in unconditionally too:
   arrays are part of the standard library, whichever extension is active. *)
module ArrayExtInstance = ArrayExt.ArrayExt (MatchExtInstance)

(* SetExt gives the set operators their meaning, as the operations of `Library.Sets`,
   so it is folded in unconditionally as well. *)
module SetExtInstance = SetExt.SetExt (ArrayExtInstance)

(* SeqExt gives the core's operators their meaning on the sequences of `Library.Seq`. *)
module SeqExtInstance = SeqExt.SeqExt (SetExtInstance)

(* Core Raven *)
module RavenCore : ExtApi.Ext = SeqExtInstance

(* ProphecyExt *)
module ProphecyExtInstance = ProphecyExt.ProphecyExt (SeqExtInstance)

(* ErrorCredits *)
module ErrorCreditsExtInstance = ErrorCreditsExt.ErrorCreditsExt (SeqExtInstance)
module SampleExtInstance = SampleExt.SampleExt (ErrorCreditsExtInstance)

let module_map ext =
  match ext with
  | DefaultExt -> (module RavenCore : ExtApi.Ext)
  | ErisExt -> (module ErrorCreditsExtInstance : ExtApi.Ext)
  | ProphecyExt -> (module ProphecyExtInstance : ExtApi.Ext)

(** Every chain reachable through a `--extension` flag, paired with that flag's name --
    i.e. exactly [ext_map], but with each tag already resolved to its module. Used only to
    build the [suggest_extension_for_*] functions below: independent of whichever chain is
    actually active for this run, so a wrong-flag error can point at whichever *other*
    chain would have worked. *)
let known_extensions : (string * (module ExtApi.Ext)) list =
  List.map ext_map ~f:(fun (name, tag) -> (name, module_map tag))

(** Given a lookup of one extension-kind's own [_is_recognized] field out of a module,
    finds the first (in [ext_map] order) `--extension` flag whose chain recognizes [tag],
    if any. *)
let suggest_extension (is_recognized : (module ExtApi.Ext) -> 'a -> bool) (tag : 'a) :
    string option =
  List.find_map known_extensions ~f:(fun (name, m) ->
      if is_recognized m tag then Some name else None)

let suggest_extension_for_type_ext (type_ext : Type.type_ext) : string option =
  suggest_extension (fun (module M : ExtApi.Ext) -> M.type_ext_is_recognized) type_ext

let suggest_extension_for_expr_ext (expr_ext : Expr.expr_ext) : string option =
  suggest_extension (fun (module M : ExtApi.Ext) -> M.expr_ext_is_recognized) expr_ext

let suggest_extension_for_stmt_ext (stmt_ext : Stmt.stmt_ext) : string option =
  suggest_extension (fun (module M : ExtApi.Ext) -> M.stmt_ext_is_recognized) stmt_ext

let suggest_extension_for_contract_ext (contract_ext : Stmt.contract_ext) : string option
    =
  suggest_extension
    (fun (module M : ExtApi.Ext) -> M.contract_ext_is_recognized)
    contract_ext

(** Extension-specific syntax tags found while walking a program's parsed (but not yet
    type-checked) AST -- see [collect_ext_tags]. Carries a location so [resolve_extension]
    can point at where a conflicting tag was found. *)
type ext_tag =
  | TypeTag of Type.type_ext * Loc.t
  | ExprTag of Expr.expr_ext * Loc.t
  | StmtTag of Stmt.stmt_ext * Loc.t

(** Walks every type/expression/statement in [m], recording each [TypeExt]/[ExprExt]/
    [BasicStmtExt]/[StmtExt] leaf it finds -- the wrapper constructors all
    extension-specific syntax funnels through (see [Type.type_ext]/[Expr.expr_ext]/
    [Stmt.stmt_ext] in astDef.ml).

    [m] is freshly parsed, not yet type-checked, so its symbol table has none of the
    per-callable/per-module scopes [Typing.check_module] would normally have created. That
    rules out [Rewriter.Module.rewrite_types]/[rewrite_expressions]/[rewrite_stmts] (the
    combinators [Rewrites.rewrites_type_ext] & co. use to reach every such leaf
    post-typecheck): their [CallDef] case calls [Rewriter.enter_callable], which does a
    [SymbolTbl.enter_exn] lookup that only a type-checked table satisfies -- on a bare
    parse it raises "Did not find subscope ... ". So this walks [Module.symbol]'s 8
    constructors by hand instead (mirroring [Rewrites.ProgStats.computeSymbolStats], which
    walks the same constructors for the same reason -- its own tbl-dependent lookups just
    happen to be satisfied there, running post-typecheck), using
    [Rewriter.Type.descend]/[Expr.descend]/[Stmt.rewrite_expressions_top] only for the
    leaf-level type/expr/stmt structure, none of which -- unlike [enter_callable] -- needs
    a pre-existing scope (see [collect_stmt]'s own doc comment on the one caveat).

    Also walks every module-instantiation argument (a functor application's [TypeArg] can
    itself be extension syntax, e.g. instantiating a generic RA with a `Proph[..]` type),
    but not [Stmt.contract_ext]: today only [DecreasesExt] defines any constructor of it,
    and that's folded into every chain alike (see [ext_map] above), so it never
    discriminates between them.

    Runs before any chain is chosen, so it can't call into any `--extension`-specific
    hook; it only pattern-matches the wrapper constructors themselves. Accumulates into a
    plain [ref] since nothing here needs the [Rewriter] state threaded at all. *)
let collect_ext_tags (m : Module.t) : ext_tag list =
  let open Rewriter.Syntax in
  let tags = ref [] in
  let rec collect_type tp =
    let* tp = Rewriter.Type.descend tp ~f:collect_type in
    (match tp with
    | Type.App (TypeExt type_ext, _, _) ->
        tags := TypeTag (type_ext, Type.to_loc tp) :: !tags
    | _ -> ());
    Rewriter.return tp
  in
  let rec collect_expr e =
    let* e = Rewriter.Expr.descend e ~f:collect_expr in
    (match e with
    | Expr.App (ExprExt expr_ext, _, _) ->
        tags := ExprTag (expr_ext, Expr.to_loc e) :: !tags
    | _ -> ());
    Rewriter.return e
  in
  (* Reaches every expression embedded in a [Basic] statement (an [Assign]'s RHS, a
     [Call]'s args, ...) as well as recursing into [Block]/[Loop]/[Cond] children --
     unlike bare [Rewriter.Stmt.descend], which only reaches the latter. Can't reuse
     [Rewriter.Stmt.rewrite_expressions] (its own top-level recursion through this same
     [rewrite_expressions_top]) as-is: its [StmtExt] arm calls
     [ext_hooks.stmt_ext_rewrite], which would hit [default_ext_hooks]'s "no extension
     configured" error since no chain is chosen yet -- so [StmtExt] is intercepted here
     before ever reaching [rewrite_expressions_top], the same "not recursed into"
     treatment [Rewriter.Stmt.descend]'s own doc comment gives it. *)
  let rec collect_stmt s =
    (match s.Stmt.stmt_desc with
    | StmtExt stmt_ext -> tags := StmtTag (stmt_ext, Stmt.to_loc s) :: !tags
    | Basic (BasicStmtExt (stmt_ext, _)) ->
        tags := StmtTag (stmt_ext, Stmt.to_loc s) :: !tags
    | _ -> ());
    match s.Stmt.stmt_desc with
    | StmtExt _ -> Rewriter.return s
    | _ -> Rewriter.Stmt.rewrite_expressions_top ~f:collect_expr ~c:collect_stmt s
  in
  (* [Rewriter.List.fold_left], not [List.iter]: nothing here needs the accumulator, but
     every element still has to run as a step of the same [Rewriter] computation. *)
  let each xs ~f = Rewriter.List.fold_left xs ~init:() ~f:(fun () x -> f x) in
  let collect_var_decl (vd : var_decl) =
    let+ (_ : type_expr) = collect_type vd.var_type in
    ()
  in
  let collect_spec (spec : Stmt.spec) =
    let+ (_ : expr) = collect_expr spec.spec_form in
    ()
  in
  let collect_module_inst_arg = function
    | Module.ModArg _ -> Rewriter.return ()
    | Module.TypeArg tp ->
        let+ (_ : type_expr) = collect_type tp in
        ()
  in
  let collect_module_inst (mi : Module.module_inst) =
    match mi.mod_inst_def with
    | None -> Rewriter.return ()
    | Some (_, args) -> each args ~f:collect_module_inst_arg
  in
  let collect_callable (c : Callable.t) =
    let* () = each c.call_decl.call_decl_formals ~f:collect_var_decl in
    let* () = each c.call_decl.call_decl_returns ~f:collect_var_decl in
    let* () = each c.call_decl.call_decl_locals ~f:collect_var_decl in
    let* () = each c.call_decl.call_decl_precond ~f:collect_spec in
    let* () = each c.call_decl.call_decl_postcond ~f:collect_spec in
    match c.call_def with
    | FuncDef { func_body = None } -> Rewriter.return ()
    | FuncDef { func_body = Some e } ->
        let+ (_ : expr) = collect_expr e in
        ()
    | ProcDef { proc_body = None } -> Rewriter.return ()
    | ProcDef { proc_body = Some s } ->
        let+ (_ : Stmt.t) = collect_stmt s in
        ()
  in
  let rec collect_symbol (sym : Module.symbol) =
    match sym with
    | ModDef md -> collect_module md
    | ModInst mi -> collect_module_inst mi
    | TypeDef td -> (
        match td.type_def_expr with
        | None -> Rewriter.return ()
        | Some tp ->
            let+ (_ : type_expr) = collect_type tp in
            ())
    | ConstrDef cd ->
        let* () = each cd.constr_args ~f:collect_var_decl in
        let+ (_ : type_expr) = collect_type cd.constr_return_type in
        ()
    | DestrDef dd ->
        let* (_ : type_expr) = collect_type dd.destr_arg in
        let+ (_ : type_expr) = collect_type dd.destr_return_type in
        ()
    | FieldDef fd ->
        let+ (_ : type_expr) = collect_type fd.field_type in
        ()
    | VarDef vd -> (
        let* (_ : type_expr) = collect_type vd.var_decl.var_type in
        match vd.var_init with
        | None -> Rewriter.return ()
        | Some e ->
            let+ (_ : expr) = collect_expr e in
            ())
    | CallDef c -> collect_callable c
  and collect_module (md : Module.t) =
    let* () = each md.mod_decl.mod_decl_formals ~f:collect_module_inst in
    let* () =
      each md.mod_decl.mod_decl_returns ~f:(fun (_, args) ->
          each args ~f:collect_module_inst_arg)
    in
    each md.mod_def ~f:(function
      | Module.Import _ -> Rewriter.return ()
      | Module.SymbolDef sym -> collect_symbol sym)
  in
  (* [Stmt.descend]'s [Block] case (reached from [collect_stmt] above) needs
     [state_ghost_scope] non-empty -- normally guaranteed by [Rewriter.enter_module]/
     [enter_callable] having pushed onto it first, which this walk deliberately never
     calls (see [collect_ext_tags]'s doc comment). [enter_ghost], unlike those, touches
     only [state_ghost_scope], not [SymbolTbl], so it's safe to call here on its own
     just to seed that stack. *)
  let pass =
    let* () = Rewriter.enter_ghost false in
    collect_module m
  in
  let (_ : SymbolTbl.t), (_ : unit) = Rewriter.eval pass (SymbolTbl.create ()) in
  List.rev !tags

(** The names of the `--extension` chains that recognize the construct [tag]. *)
let chains_recognizing (tag : ext_tag) : string list =
  List.filter_map known_extensions ~f:(fun (name, (module M : ExtApi.Ext)) ->
      let recognized =
        match tag with
        | TypeTag (t, _) -> M.type_ext_is_recognized t
        | ExprTag (e, _) -> M.expr_ext_is_recognized e
        | StmtTag (s, _) -> M.stmt_ext_is_recognized s
      in
      Option.some_if recognized name)

(** Given the tags [collect_ext_tags] found, decides which `--extension` chain the program
    needs: the first, in [ext_map] order, of the chains that recognize each of them. A
    construct that every chain recognizes, such as one of [RavenCore], leaves the choice
    open. [None] when no construct narrows it, the same fallback as when no `--extension`
    flag is given at all. Raises when no chain recognizes all tags (e.g. a file mixing
    prophecy and eris syntax), pointing at the tag that rules out the last chains and at
    the one that narrowed them to those. *)
let resolve_extension (tags : ext_tag list) : string option =
  let loc_construct = function
    | TypeTag (_, loc) -> (loc, "type")
    | ExprTag (_, loc) -> (loc, "expression")
    | StmtTag (_, loc) -> (loc, "statement")
  in
  let all_chains = List.map known_extensions ~f:fst in
  let names chains = String.concat ~sep:" or " chains in
  let possible, narrowed_by =
    List.fold tags ~init:(all_chains, None) ~f:(fun (possible, narrowed_by) tag ->
        let chains = chains_recognizing tag in
        if List.is_empty chains || List.length chains = List.length all_chains then
          (possible, narrowed_by)
        else
          let possible' = List.filter possible ~f:(List.mem chains ~equal:String.equal) in
          match (possible', narrowed_by) with
          | [], Some (tag', chains') ->
              let loc, construct = loc_construct tag in
              let loc', construct' = loc_construct tag' in
              Error.fail_with
                [
                  ( Error.Generic,
                    loc,
                    Printf.sprintf
                      "this %s belongs to the %s extension, but this file also uses a %s \
                       belonging to the %s extension; --extension auto cannot pick a \
                       single mode for it, re-run with an explicit --extension flag"
                      construct (names chains) construct' (names chains') );
                  ( Error.RelatedLoc,
                    loc',
                    Printf.sprintf "this %s belongs to the %s extension" construct'
                      (names chains') );
                ]
          | _ -> (possible', Some (tag, chains)))
  in
  Option.bind narrowed_by ~f:(fun _ -> List.hd possible)

(** Auto-detects the `--extension` chain for the already-parsed program [m]. Falls back to
    [ProphecyExt] (the "default" chain) when [m] uses no extension-specific syntax --
    matching today's behavior when no `--extension` flag is given at all. *)
let detect_extension (m : Module.t) : supported_extensions =
  match resolve_extension (collect_ext_tags m) with
  | None -> ProphecyExt
  | Some name -> List.Assoc.find_exn ~equal:String.( = ) ext_map name

(** Converts a chosen extension into the [Ast.Rewriter.ext_hooks] value the rest of the
    pipeline reads out of the [Rewriter] monad's state. *)
let to_ext_hooks (ext : (module ExtApi.Ext)) : Ast.Rewriter.ext_hooks =
  let (module Ext) = ext in
  {
    type_ext_to_name = Ext.type_ext_to_name;
    expr_ext_to_string = Ext.expr_ext_to_string;
    pr_basic_stmt_ext = Ext.pr_basic_stmt_ext;
    contract_ext_to_string = Ext.contract_ext_to_string;
    basic_stmt_ext_symbols = Ext.basic_stmt_ext_symbols;
    basic_stmt_ext_local_vars_modified = Ext.basic_stmt_ext_local_vars_modified;
    basic_stmt_ext_fields_accessed = Ext.basic_stmt_ext_fields_accessed;
    pr_stmt_ext = Ext.pr_stmt_ext;
    stmt_ext_symbols = Ext.stmt_ext_symbols;
    stmt_ext_local_vars_modified = Ext.stmt_ext_local_vars_modified;
    stmt_ext_fields_accessed = Ext.stmt_ext_fields_accessed;
    stmt_ext_atomicity = Ext.stmt_ext_atomicity;
    suggest_extension_for_type_ext;
    suggest_extension_for_expr_ext;
    suggest_extension_for_stmt_ext;
    suggest_extension_for_contract_ext;
    expr_ext_rewrite_types = Ext.expr_ext_rewrite_types;
    basic_stmt_ext_rewrite_types = Ext.basic_stmt_ext_rewrite_types;
    stmt_ext_rewrite = Ext.stmt_ext_rewrite;
    contract_ext_rewrite_exprs = Ext.contract_ext_rewrite_exprs;
    disambiguate_expr_ext = Ext.disambiguate_expr_ext;
    claim_expr = Ext.claim_expr;
    claim_location = Ext.claim_location;
    claim_basic_stmt = Ext.claim_basic_stmt;
    type_check_type_expr = Ext.type_check_type_expr;
    type_check_expr = Ext.type_check_expr;
    type_check_basic_stmt = Ext.type_check_basic_stmt;
    type_check_stmt_ext = Ext.type_check_stmt_ext;
    type_check_contract_ext = Ext.type_check_contract_ext;
    check_contract_ext_group_compatible = Ext.check_contract_ext_group_compatible;
    rewrite_type_ext = Ext.rewrite_type_ext;
    rewrite_expr_ext = Ext.rewrite_expr_ext;
    rewrite_basic_stmt_ext = Ext.rewrite_basic_stmt_ext;
    rewrite_stmt_ext = Ext.rewrite_stmt_ext;
    rewrite_contract_ext_call = Ext.rewrite_contract_ext_call;
    rewrite_callable_entry = Ext.rewrite_callable_entry;
    rewrite_contract_ext_loop_transfer = Ext.rewrite_contract_ext_loop_transfer;
  }
