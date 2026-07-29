(** AST Rewriter *)

open Base
open AstDef
open Util

module NewSymbolsTree = struct
  type node = {
    ident: ident;
    symbols: Module.symbol list;
    is_ghost: bool;
    children: t IdentMap.t;
  }
  
  and 
  t = | Node of node

  let new_node ?(is_ghost = false) ident =
    {
      ident = ident;
      is_ghost = is_ghost;
      symbols = [];
      children = Map.empty (module Ident);
    }

  let new_symbol_tree root_ident = Node (new_node root_ident)

  let rec pr ppf symbols_tree = 
    let open Stdlib.Format in
    match symbols_tree with 
    | Node node ->
      fprintf ppf "@[ {ident = %a; is_ghost = %b; symbols = %a children = %a@]" 
        Ident.pr node.ident 
        node.is_ghost 
        (Util.Print.pr_list_comma Module.pr_symbol) node.symbols
        (Util.Print.pr_map ~key:Ident.pr ~value:pr) node.children

  let to_string = Print.string_of_format pr

  let find_node qual_ident symbols_tree =
    let idents_list = QualIdent.to_list qual_ident in

    let rec scope_node_rec idents_list symbols_tree = 
      match idents_list, symbols_tree with
      | [], _ -> Some symbols_tree
      | iden :: idents, Node node ->
        match (Map.find node.children iden) with
        | Some symbol_tree ->
          scope_node_rec idents symbol_tree
        | None -> None
    in

    scope_node_rec idents_list symbols_tree

  let scope_symbols idents_list symbols_tree = 
    match find_node idents_list symbols_tree with
    | Some (Node node) -> Some node.symbols
    | None -> None

  let scope_symbols_exn idents_list symbols_tree = 
    match scope_symbols idents_list symbols_tree with
    | Some symbols -> symbols
    | None -> 
      Error.internal_error Loc.dummy "Rewriter.scope_symbols_exn: Scope symbol not found"

  let scope_is_ghost idents_list symbols_tree =
    match find_node idents_list symbols_tree with
    | Some (Node node) -> Some node.is_ghost
    | None -> None

  let scope_is_ghost_exn idents_list symbols_tree = 
    match scope_is_ghost idents_list symbols_tree with
    | Some is_ghost -> is_ghost
    | None -> 
      Error.internal_error Loc.dummy "Rewriter.scope_is_ghost_exn: Scope symbol not found"

  let create_node ?(is_ghost=false) qual_iden symbols_tree =
    let idents_list = QualIdent.to_list qual_iden in

    let rec create_path_nodes idents_list symbols_tree = 
      match idents_list, symbols_tree with
      | [], Node node -> 
        symbols_tree

      | iden :: idents, Node node -> begin
        match (Map.find node.children iden) with
        | Some child ->
          let child = create_path_nodes idents child in

          let children = Map.set node.children ~key:iden ~data:child
          in
          Node {node with children}

        | None ->
          let fresh_node = new_node ~is_ghost iden in
          let fresh_node = create_path_nodes idents (Node fresh_node) in
          let children = Map.set node.children ~key:iden ~data:fresh_node in
          Node { node with children }
        end
    in

    create_path_nodes idents_list symbols_tree

  let clear_node qual_iden symbols_tree =
    let idents_list = QualIdent.to_list qual_iden in

    let rec clear_node_rec idents_list symbols_tree =
      match idents_list, symbols_tree with
      | [], Node node -> 
        Node { node with symbols = []; children = Map.empty (module Ident); }
      | [iden], Node node -> begin
          match (Map.find node.children iden) with 
          | None -> 
            symbols_tree
            
          | Some (Node child) ->
            let children = Map.remove node.children iden in
            Node { node with children }
        end
      | iden :: idents, Node node ->
        match (Map.find node.children iden) with
        | None -> symbols_tree

        | Some child ->
          let child = clear_node_rec idents child in
          let children = (Map.set node.children ~key:iden ~data:child) in

          Node { node with children }
    in

    clear_node_rec idents_list symbols_tree

  let scope_is_ghost qual_ident symbols_tree = 
    match find_node qual_ident symbols_tree with
    | Some (Node node) -> Some node.is_ghost
    | None -> None

  let scope_add_symbols qual_ident symbols_list symbols_tree =
    let ident_list = QualIdent.to_list qual_ident in

    let rec scope_add_symbols_rec ident_list symbols_list symbols_tree =
      match ident_list, symbols_tree with
      | [], Node node -> 
        Node { node with symbols = symbols_list @ node.symbols }

      | ident :: idents, Node node ->
        match (Map.find node.children ident) with
        | None -> Error.internal_error Loc.dummy "Rewriter.scope_add_symbols: Scope not found"
        | Some child ->
          let child = scope_add_symbols_rec idents symbols_list child in
          let children = Map.set node.children ~key:ident ~data:child in
          Node { node with children }

    in

    let symbols_tree = create_node qual_ident symbols_tree in

    scope_add_symbols_rec ident_list symbols_list symbols_tree
end


(* [ext_hooks] bundles every function an active language extension contributes to the
   core pipeline (see lib/ext/README.md). It has to be defined mutually with [state]/[t]
   because several of its fields return [_ t]. A value of this type is installed once,
   by [eval] below, and threaded through the rest of the pipeline as ordinary monadic
   state -- there is no global mutable reference standing in for "the active extension". *)
type 'a state = {
  state_table : SymbolTbl.t;
  state_update_table : bool;
  state_new_symbols_tree : NewSymbolsTree.t;
  state_ghost_scope : bool list;
  (* Stack mirroring [state_ghost_scope]: true inside a [MachineFree] (not [UserFree])
     scope. See [resolve_and_find_opt]'s fallback, the only consumer. *)
  state_relaxed_lookup : bool list;
  state_user_data : 'a;
  state_ext_hooks : ext_hooks;
}

and ('a, 'b) t_ext = 'b state -> 'b state * 'a
and 'a t = ('a, unit) t_ext

(** Callback bundle Typing.ml hands to [ext_hooks.type_check_type_expr] so an extension
    can recursively process sub-type-expressions using the core type-checker. *)
and type_check_type_expr_functs = {
  process_type_expr : type_expr -> type_expr t;
}

(** Callback bundle Typing.ml hands to [ext_hooks.type_check_expr]. *)
and type_check_expr_functs = {
  check_and_set : expr -> type_expr -> type_expr -> type_expr -> expr t;
  process_expr : expr -> type_expr -> expr t;
  type_mismatch_error : 'a. location -> type_expr -> type_expr -> 'a;
  expand_type_expr : type_expr -> (type_expr, unit) t_ext;
}

(** Callback bundle Typing.ml hands to [ext_hooks.type_check_stmt]. *)
and type_check_stmt_functs = {
  get_assign_lhs :  is_init:bool ->
                    ?is_ghost_cmd:bool ->
                    qual_ident ->
                    unit state ->
                    unit state * (qual_ident * var_decl);

  expand_type_expr : type_expr -> (type_expr, unit) t_ext;

  disambiguate_process_expr : expr -> type_expr -> DisambiguationTbl.t -> expr t;

  type_mismatch_error : 'a. location -> type_expr -> type_expr -> 'a;

  disam_tbl_add_var_decl : var_decl -> DisambiguationTbl.t -> var_decl * DisambiguationTbl.t;

  process_symbol : Module.symbol -> Module.symbol t;
}

(** The complete set of extension callbacks: printing/query hooks for the [*_ext]
    leaves of the AST (see AstDef's [make_printers]/[make_symbols]/etc.), the
    type-rewriting hooks used deep inside generic traversal, and the type-checking /
    rewriting entry points an extension implements (see [ExtApi.Ext] in
    lib/ext/api/extApi.ml, which every concrete extension satisfies). Built once from
    the CLI-selected extension by [lib/ext/ext.ml] and installed by [eval]. *)
and ext_hooks = {
  type_ext_to_name : Type.type_ext -> string;
  expr_ext_to_string : Expr.expr_ext -> string;
  pr_stmt_ext : Stdlib.Format.formatter -> Stmt.stmt_ext -> expr list -> unit;
  contract_ext_to_string : Stmt.contract_ext -> string;
  stmt_ext_symbols : Stmt.stmt_ext -> QualIdentSet.t;
  stmt_ext_local_vars_modified : Stmt.stmt_ext -> expr list -> ident list;
  stmt_ext_fields_accessed : Stmt.stmt_ext -> expr list -> qual_ident list;

  (** Best-effort "did you mean" lookup: given a [*_ext] tag the *active* extension
      chain didn't recognize, checks whether some *other* known [--extension] choice
      would have, and if so returns that flag's name. [None] means no known extension
      anywhere recognizes the construct -- a genuine internal error, not a
      wrong-flag situation. Independent of which chain is currently active (computed
      once, up front, from every entry in [lib/ext/ext.ml]'s [ext_map]); used only to
      turn the [DefaultExt] "no active extension recognizes this ..." fallback into an
      actionable message. *)
  suggest_extension_for_type_ext : Type.type_ext -> string option;
  suggest_extension_for_expr_ext : Expr.expr_ext -> string option;
  suggest_extension_for_stmt_ext : Stmt.stmt_ext -> string option;
  suggest_extension_for_contract_ext : Stmt.contract_ext -> string option;

  expr_ext_rewrite_types : f:(type_expr -> type_expr t) -> Expr.expr_ext -> Expr.expr_ext t;
  stmt_ext_rewrite_types : f:(type_expr -> type_expr t) -> Stmt.stmt_ext -> Stmt.stmt_ext t;

  (** Applies [f] to every expression a [contract_ext] value carries (e.g. each
      measure's [spec_form] for [decreases]), for the same reason
      [stmt_ext_rewrite_types] exists: generic substitution during things like module
      instantiation, where core code needs to rewrite every expression in a callable's
      contract uniformly without knowing what a given [contract_ext] means. *)
  contract_ext_rewrite_exprs : f:(expr -> expr t) -> Stmt.contract_ext -> Stmt.contract_ext t;

  type_check_type_expr : Type.type_ext -> type_expr list -> Type.type_attr -> type_check_type_expr_functs -> type_expr t;
  type_check_expr : Expr.expr_ext -> expr list -> Expr.expr_attr -> type_expr -> type_check_expr_functs -> expr t;
  type_check_stmt :
    Callable.call_decl ->
    Stmt.stmt_ext -> expr list ->
    location ->
    DisambiguationTbl.t ->
    type_check_stmt_functs ->
    (Stmt.basic_stmt_desc * DisambiguationTbl.t) t;

  type_check_contract_ext :
    Callable.call_decl ->
    Stmt.contract_ext ->
    location ->
    DisambiguationTbl.t ->
    type_check_stmt_functs ->
    Stmt.contract_ext t;

  (** Called once per module for every group of mutually-recursive callables (a
      strongly-connected component of the call graph with more than one member), given
      every member's [call_decl] -- see [ExtApi.Ext.check_contract_ext_group_compatible]
      for why this can't just be folded into [type_check_contract_ext]. Default (no
      active contract extension) is to do nothing. *)
  check_contract_ext_group_compatible : Callable.call_decl list -> unit t;

  rewrite_type_ext : Type.type_ext -> type_expr list -> location -> type_expr t;
  rewrite_expr_ext : Expr.expr_ext -> expr list -> Expr.expr_attr -> expr t;
  rewrite_stmt_ext : Stmt.stmt_ext -> expr list -> location -> Stmt.t t;

  (** [caller_call_decl -> callee_call_decl -> in_same_scc -> call_args -> loc -> ...] --
      see [ExtApi.Ext.rewrite_contract_ext_call]'s doc comment for the full contract;
      [in_same_scc] says whether caller and callee lie in the same strongly-connected
      component of the module's call graph (self-recursion included, as the
      size-1-with-self-loop case), computed once per module by
      [lib/frontend/rewrites/rewrites.ml]. *)
  rewrite_contract_ext_call :
    Callable.call_decl -> Callable.call_decl -> bool -> expr list -> location -> Stmt.t list t;

  (** Called once for every [Proc]/[Lemma] callable, before any of its statements are
      visited elsewhere. Returns statements to prepend at the very top of the
      callable's body. General-purpose, not tied to [contract_ext]: any extension can
      use it for whatever per-callable body setup it needs (e.g. introducing and
      initializing ghost locals sized to that specific callable, as [DecreasesExt]
      does for its `decreases` measure snapshot). Default (no extension using this
      hook) is to prepend nothing. *)
  rewrite_callable_entry : Callable.call_decl -> Stmt.t list t;

  (** Called by [rewrite_loops] as it transfers a loop's [loop_contract_ext] entries
      onto the synthesized tail-recursive procedure's [call_decl_contract_ext]. [subst]
      is the same substitution [rewrite_loops] applies to [loop_contract] (loop-local
      variables -> the synthesized procedure's fresh formals); an extension applies it
      to whatever expressions its value carries, and may also swap in loop-specific
      wording (e.g. via a payload that reuses [Stmt.spec]'s [spec_error], the same
      mechanism [rewrite_stmt_error_msg]'s [Loop] case already uses for invariants) --
      capturing the original location before calling [subst], not after, since
      substituting a bare-identifier expression replaces the whole node. Pure: default
      (no active contract extension, or a tag the extension doesn't recognize) is the
      identity. *)
  rewrite_contract_ext_loop_transfer : subst:(expr -> expr) -> Stmt.contract_ext -> Stmt.contract_ext;
}

(** What every [Rewriter.t] computation sees before any extension has been installed.
    [eval] below always installs the real hooks for the CLI-selected extension; this
    default only matters for entry points (e.g. the backend, which only ever runs on
    already-rewritten, extension-free ASTs) that never exercise it. *)
let default_ext_hooks : ext_hooks = {
  type_ext_to_name = Type.default_type_ext_to_name;
  expr_ext_to_string = Expr.default_expr_ext_to_string;
  pr_stmt_ext = Stmt.default_pr_stmt_ext;
  contract_ext_to_string = Stmt.default_contract_ext_to_string;
  stmt_ext_symbols = Stmt.default_stmt_ext_symbols;
  stmt_ext_local_vars_modified = Stmt.default_stmt_ext_local_vars_modified;
  stmt_ext_fields_accessed = Stmt.default_stmt_ext_fields_accessed;
  suggest_extension_for_type_ext = (fun _ -> None);
  suggest_extension_for_expr_ext = (fun _ -> None);
  suggest_extension_for_stmt_ext = (fun _ -> None);
  suggest_extension_for_contract_ext = (fun _ -> None);
  expr_ext_rewrite_types =
    (fun ~f:_ _ -> Error.internal_error Loc.dummy "Rewriter.default_ext_hooks.expr_ext_rewrite_types: no extension configured");
  stmt_ext_rewrite_types =
    (fun ~f:_ _ -> Error.internal_error Loc.dummy "Rewriter.default_ext_hooks.stmt_ext_rewrite_types: no extension configured");
  contract_ext_rewrite_exprs =
    (fun ~f:_ _ -> Error.internal_error Loc.dummy "Rewriter.default_ext_hooks.contract_ext_rewrite_exprs: no extension configured");
  type_check_type_expr =
    (fun _ _ _ _ -> Error.internal_error Loc.dummy "Rewriter.default_ext_hooks.type_check_type_expr: no extension configured");
  type_check_expr =
    (fun _ _ _ _ _ -> Error.internal_error Loc.dummy "Rewriter.default_ext_hooks.type_check_expr: no extension configured");
  type_check_stmt =
    (fun _ _ _ _ _ _ -> Error.internal_error Loc.dummy "Rewriter.default_ext_hooks.type_check_stmt: no extension configured");
  type_check_contract_ext =
    (fun _ _ _ _ _ -> Error.internal_error Loc.dummy "Rewriter.default_ext_hooks.type_check_contract_ext: no extension configured");
  check_contract_ext_group_compatible =
    (fun _ -> Error.internal_error Loc.dummy "Rewriter.default_ext_hooks.check_contract_ext_group_compatible: no extension configured");
  rewrite_type_ext =
    (fun _ _ _ -> Error.internal_error Loc.dummy "Rewriter.default_ext_hooks.rewrite_type_ext: no extension configured");
  rewrite_expr_ext =
    (fun _ _ _ -> Error.internal_error Loc.dummy "Rewriter.default_ext_hooks.rewrite_expr_ext: no extension configured");
  rewrite_stmt_ext =
    (fun _ _ _ -> Error.internal_error Loc.dummy "Rewriter.default_ext_hooks.rewrite_stmt_ext: no extension configured");
  rewrite_contract_ext_call =
    (fun _ _ _ _ _ -> Error.internal_error Loc.dummy "Rewriter.default_ext_hooks.rewrite_contract_ext_call: no extension configured");
  rewrite_callable_entry =
    (fun _ -> Error.internal_error Loc.dummy "Rewriter.default_ext_hooks.rewrite_callable_entry: no extension configured");
  rewrite_contract_ext_loop_transfer = (fun ~subst:_ tag -> tag);
}


(* Using pointers to access certain functions from Typing in certain context while circumventing dependency cycles. *)

(** This is meant to point to:
      Typing.process_symbol
    It is initialized at the end of Typing.ml.
*)
let process_symbol_ref : 'a. (Module.symbol -> Module.symbol t) ref = ref (
  fun _ -> Error.unsupported_error Loc.dummy "Rewriter.process_symbol_ref uninitialized"
)

(** This is meant to point to:
      Typing.expand_type_expr
    It is initialized at the end of Typing.ml.
*)
let expand_type_expr_ref : (
    type_expr -> (type_expr, unit) t_ext
  ) ref
    = ref (fun _ -> Error.internal_error Loc.dummy "Rewriter.expand_type_expr_ref uninitialized")


include State

let eval ?(update = true) ?(ext_hooks = default_ext_hooks) m tbl =
  let sin =
    {
      state_table = tbl;
      state_update_table = update;
      state_new_symbols_tree = NewSymbolsTree.new_symbol_tree (QualIdent.to_ident tbl.tbl_root.scope_id);
      state_ghost_scope = [];
      state_relaxed_lookup = [];
      state_user_data = ();
      state_ext_hooks = ext_hooks;
    }
  in
  let sout, res = m sin in

  (sout.state_table, res)

let eval_with_user_state ~init (f : 'a state -> 'a state * 'b) : 'b t =
 fun st ->
  let st, v = f { st with state_user_data = init } in

  let st = { st with state_user_data = () } in
  (st, v)

let init s _ = (s, ())
let get_table s = (s, s.state_table)
let current_ext_hooks s = (s, s.state_ext_hooks)

type printers = {
  pr_type : Stdlib.Format.formatter -> type_expr -> unit;
  pr_type_var_decl : Stdlib.Format.formatter -> var_decl -> unit;
  pr_type_var_decl_list : Stdlib.Format.formatter -> var_decl list -> unit;
  pr_expr : Stdlib.Format.formatter -> expr -> unit;
  pr_expr_list : Stdlib.Format.formatter -> expr list -> unit;
  pr_stmt : Stdlib.Format.formatter -> Stmt.t -> unit;
  pr_stmt_basic : Stdlib.Format.formatter -> Stmt.basic_stmt_desc -> unit;
  pr_stmt_spec_list : string -> Stdlib.Format.formatter -> Stmt.spec list -> unit;
  pr_callable : Stdlib.Format.formatter -> Callable.t -> unit;
  pr_module : Stdlib.Format.formatter -> Module.t -> unit;
  pr_symbol : Stdlib.Format.formatter -> Module.symbol -> unit;
  symbol_to_string : Module.symbol -> string;
}

(** The extension-aware sibling of AstDef's default printers ([Type.pr], [Stmt.pr],
    etc.): built from the given extension hooks. Use this (rather than the bare
    [Type.pr]/[Stmt.pr]/...) in debug logging or error messages that might run over
    an AST that can still contain [*_ext] nodes, i.e. before [Rewrites.process_module]
    has rewritten them away. Most callers want [current_printers] below, which reads
    the hooks out of the active [Rewriter.t] state; this pure version exists for the
    handful of call sites (e.g. [bin/raven.ml]) that only have an [ext_hooks] value,
    not a running computation, in scope. *)
let printers_of_ext_hooks (h : ext_hooks) : printers =
  let (_, pr_type, pr_type_var_decl, pr_type_var_decl_list, _, _, _, _, _, _) =
    Type.make_printers ~type_ext_to_name:h.type_ext_to_name
  in
  let (_, _, _, pr_expr, pr_expr_list, _, _, _, _, _, _, _) =
    Expr.make_printers ~type_ext_to_name:h.type_ext_to_name
      ~expr_ext_to_string:h.expr_ext_to_string
  in
  let (_, pr_stmt_spec_list, pr_stmt_basic, pr_stmt, _, _, _) =
    Stmt.make_printers ~type_ext_to_name:h.type_ext_to_name
      ~expr_ext_to_string:h.expr_ext_to_string ~pr_stmt_ext:h.pr_stmt_ext
      ~contract_ext_to_string:h.contract_ext_to_string
  in
  let (_, _, pr_callable) =
    Callable.make_printers ~type_ext_to_name:h.type_ext_to_name
      ~expr_ext_to_string:h.expr_ext_to_string ~pr_stmt_ext:h.pr_stmt_ext
      ~contract_ext_to_string:h.contract_ext_to_string
  in
  let (pr_module, _, _, _) =
    Module.make_printers ~type_ext_to_name:h.type_ext_to_name
      ~expr_ext_to_string:h.expr_ext_to_string ~pr_stmt_ext:h.pr_stmt_ext
      ~contract_ext_to_string:h.contract_ext_to_string
  in
  let (pr_symbol, symbol_to_string) =
    Symbol.make_printers ~type_ext_to_name:h.type_ext_to_name
      ~expr_ext_to_string:h.expr_ext_to_string ~pr_stmt_ext:h.pr_stmt_ext
      ~contract_ext_to_string:h.contract_ext_to_string
  in
  { pr_type; pr_type_var_decl; pr_type_var_decl_list; pr_expr; pr_expr_list;
    pr_stmt; pr_stmt_basic; pr_stmt_spec_list; pr_callable; pr_module; pr_symbol;
    symbol_to_string }

(** [current_printers] reads the active extension's hooks out of the [Rewriter.t]
    state -- see [printers_of_ext_hooks] for the pure/no-state version. *)
let current_printers (s : 'a state) : 'a state * printers =
  (s, printers_of_ext_hooks s.state_ext_hooks)

(* Captured before [Logs] is shadowed below, for the rest of this file to use when
   logging something that doesn't need [printers] (plain values, no AST fragments). *)
module Stdlib_logs = Logs

(** Rewriter-aware counterparts of [Logs.debug]/[info]/[warn]/[err]/[app]: each takes
    a closure that -- in addition to the usual message-construction function [m] --
    also receives the [printers] for whichever extension is active in the current
    state.

    The printer lookup happens inside the closure handed to the underlying [Logs]
    function, so -- exactly as with plain [Logs.debug] -- it is skipped entirely
    when the corresponding log level isn't enabled. *)
module Logs = struct
  let lift (log : ('a, unit) Stdlib_logs.msgf -> unit)
      (f : printers -> ('a, unit) Stdlib_logs.msgf) (s : 'st state) : 'st state * unit =
    log (fun m -> f (printers_of_ext_hooks s.state_ext_hooks) m);
    (s, ())

  let debug f = lift Stdlib_logs.debug f
  let info f = lift Stdlib_logs.info f
  let warn f = lift Stdlib_logs.warn f
  let err f = lift Stdlib_logs.err f
  let app f = lift Stdlib_logs.app f
end

(** Warning: should only be used for debugging purposes *)
let __get_state s = (s, s)

let current_scope s : 'a state * SymbolTbl.scope = (s, s.state_table.tbl_curr)

let current_scope_id s : 'a state * qual_ident =
  (s, s.state_table.tbl_curr.scope_id)

let current_scope_children s : 'a state * SymbolTbl.scope IdentHashtbl.t =
  (s, s.state_table.tbl_curr.scope_children)

let current_scope_entries s : 'a state * SymbolTbl.entry IdentHashtbl.t =
  (s, s.state_table.tbl_curr.scope_entries)

let current_user_state s : 'a state * 'a = (s, s.state_user_data)
let set_user_state user_data s = ({ s with state_user_data = user_data }, ())

let current_module_name s : 'a state * qual_ident =
  let s, curr_scope = current_scope s in

  if curr_scope.scope_is_local then (s, QualIdent.pop curr_scope.scope_id)
  else
    (* Logs.warn (fun m -> m "Rewrites.generate_inv_function: Expected a local scope, but got a non-local scope: %a" QualIdent.pr curr_scope.scope_id); *)
    (s, curr_scope.scope_id)

let update_table f s = ({ s with state_table = f s.state_table }, ())

let is_ghost_scope s = 
  let _, scope_id = current_scope_id s in
  (s, NewSymbolsTree.scope_is_ghost_exn scope_id s.state_new_symbols_tree || Base.List.hd s.state_ghost_scope |> Base.Option.value ~default:false)

let exit_ghost s = ({ s with state_ghost_scope = Base.List.tl_exn s.state_ghost_scope }, ())
let enter_ghost b s = ({ s with state_ghost_scope = b :: s.state_ghost_scope }, ())

let is_relaxed_lookup s =
  (s, Base.List.hd s.state_relaxed_lookup |> Base.Option.value ~default:false)
let exit_relaxed_lookup s = ({ s with state_relaxed_lookup = Base.List.tl_exn s.state_relaxed_lookup }, ())
let enter_relaxed_lookup b s = ({ s with state_relaxed_lookup = b :: s.state_relaxed_lookup }, ())

(** Looks [qual_ident] up directly in the flat table of all fully-qualified symbols
    seen so far, bypassing [resolve]'s scope-relative guard/alias-chasing. Only valid
    for qualidents that already resolved successfully once before. *)
let find_absolute qual_ident s = (s, Base.Map.find s.state_table.tbl_symbols qual_ident)

let exit_block s = exit_ghost s
let enter_block block s =
  let is_ghost_scope = Base.List.hd_exn s.state_ghost_scope || block.Stmt.block_is_ghost in
  enter_ghost is_ghost_scope s

let rec module_add_descendants (mdef: Module.t) (new_symbols_node: NewSymbolsTree.t) =
  let open Module in
  match new_symbols_node with Node node ->

  let new_symbols, mod_def = Base.List.fold_map mdef.mod_def ~init:[] ~f:(fun accum instr ->
    match instr with
    | Import _ -> accum, instr
    | SymbolDef (ModDef mdef' as symbol)  -> begin
      match (Map.find node.children (Symbol.to_name symbol)) with
      | None -> accum, (SymbolDef symbol)
      | Some child -> 
        let mdef' = module_add_descendants mdef' child in
        accum, SymbolDef (ModDef mdef')
      end
    | SymbolDef (CallDef call_def as symbol) -> begin
      match (Map.find node.children (Symbol.to_name symbol)) with
      | None -> accum, (SymbolDef symbol)
      | Some (Node child) ->
        
        let new_locals, new_mod_symbols =
        Base.List.partition_map child.symbols ~f:(function
          | VarDef ({ var_init = None; _ } as var_def) ->
              First var_def.var_decl
          | symbol -> Second symbol)
        in
        let call_decl =
          {
            call_def.call_decl with
            call_decl_locals =
              Base.List.rev_append new_locals call_def.call_decl.call_decl_locals;
          }
        in
          let call_def = { call_def with call_decl }
      in
      new_mod_symbols @ accum, SymbolDef (CallDef call_def)

      end
    | _ -> accum, instr
  )
  in

  let new_instr = Base.List.rev_map ~f:(fun def -> SymbolDef def) (node.symbols @ new_symbols) in

  let mdef = { mdef with mod_def = new_instr @ mod_def} in 

  mdef

let exit_module (mdef : Module.t) s =
  (* Logs.debug (fun m -> m "exit_module: %a" Module.pr (mdef)); *)
  let tbl = s.state_table in
  let _, scope_id = current_scope_id s in
  let state_new_symbols_tree, mdef = 
    match NewSymbolsTree.find_node scope_id s.state_new_symbols_tree with
    | None ->
      s.state_new_symbols_tree, mdef

    | Some child ->
      let mdef = module_add_descendants mdef child in

      let state_new_symbols_tree = NewSymbolsTree.clear_node scope_id s.state_new_symbols_tree in

      (state_new_symbols_tree, mdef)
  in

  let state_ghost_scope = Base.List.tl_exn s.state_ghost_scope in
  let state_relaxed_lookup = Base.List.tl_exn s.state_relaxed_lookup in
  ( { s with
      state_table = SymbolTbl.exit tbl;
      state_new_symbols_tree;
      state_ghost_scope;
      state_relaxed_lookup;
    }, mdef )

let exit_callable (call_def : Callable.t) s =
  (*Logs.debug (fun m ->
      m "exit_callable: %a" Ident.pr call_def.call_decl.call_decl_name);*)

  (* (match call_def.call_def with
     | Callable.FuncDef { func_body = Some _; _ } -> ()
     | Callable.ProcDef { proc_body = Some pp; _ } ->
      Logs.debug (fun m -> m "exit_callable: proc_body = %a" AstDef.Stmt.pr pp);
     | _ -> ()); *)
  let tbl = s.state_table in
  let _, scope_id = current_scope_id s in
  let state_new_symbols_tree, call_def =
    match NewSymbolsTree.find_node scope_id s.state_new_symbols_tree with
    | None ->
      s.state_new_symbols_tree, call_def

    | Some (Node node) ->
      let open Callable in
      let new_locals, new_mod_symbols =
          Base.List.partition_map node.symbols ~f:(function
            | VarDef ({ var_init = None; _ } as var_def) ->
                First var_def.var_decl
            | symbol -> Second symbol)
      in
      let call_decl =
        {
          call_def.call_decl with
          call_decl_locals =
            Base.List.rev_append new_locals call_def.call_decl.call_decl_locals;
        }
      in
      let call_def = { call_def with call_decl } in

      let state_new_symbols_tree = NewSymbolsTree.scope_add_symbols (QualIdent.pop scope_id) new_mod_symbols s.state_new_symbols_tree in
      let state_new_symbols_tree = NewSymbolsTree.clear_node scope_id state_new_symbols_tree in

      state_new_symbols_tree, call_def
  in

  let state_ghost_scope = Base.List.tl_exn s.state_ghost_scope in
  let state_relaxed_lookup = Base.List.tl_exn s.state_relaxed_lookup in
  ( { s with state_table = SymbolTbl.exit tbl; state_new_symbols_tree; state_ghost_scope; state_relaxed_lookup },
    call_def )

let enter symbol s =
  (*Logs.debug (fun m ->
      m "Rewriter.enter: symbol = %a" Ident.pr (AstDef.Symbol.to_name symbol));*)
  (* Logs.debug (fun m -> m "Rewriter.enter: symbol = %a" Symbol.pr (symbol)); *)
  let is_ghost_scope =
    match symbol with
    | Module.CallDef { call_decl = { call_decl_kind = (Lemma | Pred); _}; _ } -> true
    | ModDef _ | CallDef _ -> false
    | _ -> failwith "enter: expected module or callable symbol"
  in
  (* [MachineFree] only: a user-marked [UserFree] symbol's contract isn't pre-validated,
     so it must not enable [resolve_and_find_opt]'s relaxed-lookup fallback. *)
  let is_free_scope =
    match symbol with
    | Module.CallDef { call_decl = { call_decl_status = MachineFree; _ }; _ } -> true
    | ModDef { mod_decl = { mod_decl_status = MachineFree; _ }; _ } -> true
    | _ -> false
  in
  let relaxed_lookup =
    is_free_scope || (Base.List.hd s.state_relaxed_lookup |> Base.Option.value ~default:false)
  in
  let symbol_ident = Symbol.to_name symbol in
  let _, scope_id = current_scope_id s in
  let state_new_symbols_tree = NewSymbolsTree.create_node ~is_ghost:is_ghost_scope (QualIdent.append scope_id symbol_ident) s.state_new_symbols_tree in
  ( {
      s with
      state_table = SymbolTbl.enter_exn symbol_ident s.state_table;
      state_ghost_scope = is_ghost_scope :: s.state_ghost_scope;
      state_relaxed_lookup = relaxed_lookup :: s.state_relaxed_lookup;
      state_new_symbols_tree;
    },
    () )

let enter_module mdef = enter (ModDef mdef)

let enter_callable callable =
  (*Logs.debug (fun m -> m "Rewriter.enter_callable: callable ");*)
  enter (CallDef callable)

let declare_symbol symbol : unit t = update_table (SymbolTbl.add_symbol symbol)

let introduce_symbol symbol s =
  let _, scope_id = current_scope_id s in
  let state_new_symbols_tree = NewSymbolsTree.scope_add_symbols scope_id [symbol] s.state_new_symbols_tree in
  ( {
      s with
      state_table =
        (if s.state_update_table then SymbolTbl.add_symbol symbol s.state_table
         else s.state_table);
        state_new_symbols_tree;
      (* state_new_symbols =
        (match s.state_new_symbols with
        | scope :: new_symbols -> (symbol :: scope) :: new_symbols
        | _ -> failwith "empty scope"); *)
    },
    () )

(* `f` represents a typechecking function that will be used to type-check 
 * `symbol` once the state has been set in the correct scope. 
 * This function is almost always intended to be `Typing.process_symbol` function. 
 * However, this cannot be set statically since 
 * that creates a recursive dependency between `module Rewriter` and `module Typing`. *)
let introduce_typecheck_symbols ~loc
    ~(f : AstDef.Module.symbol -> AstDef.Module.symbol t)
    (symbols : Module.symbol list) (s : 'a state) : 'a state * qual_ident list =

  let s, () = Logs.debug (fun printers m -> m
    "Rewriter.introduce_typecheck_symbols: symbols = %a"
      (Util.Print.pr_list_comma (fun ppf symbol -> Stdlib.Format.fprintf ppf "%a -> %a" AstDef.Ident.pr (AstDef.Symbol.to_name symbol) printers.pr_symbol symbol)) (symbols)
  ) s in

  let current_scope = s.state_table.tbl_curr.scope_id in
  let symbol__qual_idents = Base.List.map ~f:(fun symbol -> symbol, (QualIdent.append current_scope (Symbol.to_name symbol))) symbols in

  Stdlib_logs.debug (fun m -> m
    "
      Rewriter.introduce_typecheck_symbols: current_scope = %a \n \
      Rewriter.introduce_typecheck_symbols: qual_ident = %a \n \
    "
      QualIdent.pr current_scope
      (Util.Print.pr_list_comma QualIdent.pr) (snd (Base.List.unzip symbol__qual_idents))
  );

  let s, symbol__qual_idents__already_defineds = Base.List.fold_map ~init:s symbol__qual_idents ~f:(fun s (symbol, qual_iden) ->
    let (s, _), already_defined = 
        try (declare_symbol symbol s, false) with _ -> 
          ((s, ()), true)  
    in
    s, (symbol, qual_iden, already_defined)
  )  in

  (* if symbol is getting added to parent scope (see appropriate_scope in SymbolTbl.add_symbol, then we need to go to parent scope before calling `f` on `symbol`) *)
  let s, (symbol__qual_idents) = Base.List.fold_map ~init:s symbol__qual_idents__already_defineds ~f:(fun s (symbol, qual_ident, already_defined) ->
    match symbol with
    | VarDef _ ->
        if not already_defined then 
          let (s, symbol) = f symbol s in 
          s, (symbol, qual_ident)
        else (s, (symbol, qual_ident))
    | _ ->
        let s, () = Logs.debug (fun printers m -> m
            "Rewriter.introduce_typecheck_symbols: Starting to type-check: %a "
            printers.pr_symbol symbol
          ) s in

        if s.state_table.tbl_curr.scope_is_local then
          let curr_scope_name = s.state_table.tbl_curr.scope_id.qual_base in

          let s = { s with 
            state_table = SymbolTbl.exit s.state_table;
            }
          in

          let s, symbol =
            if not already_defined then f symbol s else (s, symbol)
          in

          let qual_ident =
            QualIdent.append s.state_table.tbl_curr.scope_id
              (Symbol.to_name symbol)
          in

          let s = { s with
              state_table = SymbolTbl.enter_exn curr_scope_name s.state_table;
            }
          in

          (s, (symbol, qual_ident))
        else 
          let s, symbol = f symbol s in
          s, (symbol, qual_ident)
  )
  in

  let symbols, qual_idents = Base.List.unzip symbol__qual_idents in

  let s, () = Logs.debug (fun printers m ->
      m "Rewriter.introduce_typecheck_symbol end: symbols = %a" (Print.pr_list_comma printers.pr_symbol) symbols) s in

  ( { s with
      state_new_symbols_tree = NewSymbolsTree.scope_add_symbols current_scope symbols s.state_new_symbols_tree;
    }, 
    qual_idents )

let introduce_typecheck_symbol ~loc
    ~(f : AstDef.Module.symbol -> AstDef.Module.symbol t)
    (symbol : Module.symbol) (s : 'a state) : 'a state * qual_ident =

  let s, qual_idents = introduce_typecheck_symbols ~loc ~f [symbol] s in
  
  s, Base.List.hd_exn qual_idents


let introduce_typecheck_symbol' ~loc
    (symbol : Module.symbol) (s : 'a state) : 'a state * qual_ident =
  introduce_typecheck_symbol ~loc ~f:!process_symbol_ref symbol s

let introduce_typecheck_symbol_at_scope' ~loc
    (symbol: Module.symbol) (scope_qi: qual_ident) (s: 'a state) : 'a state * qual_ident =

  let _, start_scope_id = current_scope_id s in

  let s = { s with
    state_table = SymbolTbl.goto_scope scope_qi s.state_table
  } in

  Stdlib_logs.debug (fun m -> m "introduce_typecheck_symbol_at_scope': scope_qi=%a; after goto, cuurent_scope: %a; symbol = %a " QualIdent.pr scope_qi QualIdent.pr s.state_table.tbl_curr.scope_id Ident.pr (Symbol.to_name symbol));

  let s, _ = declare_symbol symbol s in
  let s, symbol = !process_symbol_ref symbol s in

  let state_new_symbols_tree = NewSymbolsTree.scope_add_symbols scope_qi [symbol] s.state_new_symbols_tree in

  let s = { s with
    state_table = SymbolTbl.goto_scope start_scope_id s.state_table;
    state_new_symbols_tree;
  } in

  let symbol_qual_ident = (QualIdent.append scope_qi (Symbol.to_name symbol)) in

  (* Logs.debug (fun m -> m "Rewriter.introduce_typecheck_symbol_at_scope: symbol_qual_ident = %a" QualIdent.pr symbol_qual_ident); *)
  (s, symbol_qual_ident)


let add_locals var_decls s =
  if s.state_update_table then (
    (*Logs.debug (fun m ->
        m "Rewriter.add_locals: var_decls = %a"
          (Print.pr_list_comma AstDef.Ident.pr)
          (List.map var_decls ~f:(fun (vd : var_decl) -> vd.var_name)));*)
    update_table (SymbolTbl.add_local_vars var_decls) s)
  else (s, ())

let add_call_decl_locals (call_decl : Callable.call_decl) =
  let open Syntax in
  let+ _ = add_locals call_decl.call_decl_formals
  and+ _ = add_locals call_decl.call_decl_returns
  and+ _ = add_locals call_decl.call_decl_locals in
  ()

let set_symbol symbol s =
  (* Logs.debug (fun m -> m "Rewriter.set_symbol: symbol = %a" AstDef.Ident.pr (AstDef.Symbol.to_name symbol)); *)
  (* Logs.debug (fun m -> m "Rewriter.set_symbol: symbol = %a" Symbol.pr symbol); *)
  if s.state_update_table then
    ({ s with state_table = SymbolTbl.set_symbol symbol s.state_table }, ())
  else (s, ())

let import import_instr s =
  ({ s with state_table = SymbolTbl.import import_instr s.state_table }, ())

let wrap_user_state_rewriter (f : 'a state -> 'a state * 'b) (s : unit state) :
    'a state * 'b =
  f s


module VarDecl = struct
  let rewrite_types ~f var_decl : (var_decl, 'a) t_ext =
    let open Syntax in
    let+ var_type = f var_decl.AstDef.Type.var_type in
    { var_decl with var_type }
end

module Type = struct
  let descend ~f (tp_expr : Type.t) : (Type.t, 'a) t_ext =
    let open Syntax in
    match tp_expr with
    | App (constr, tp_list, tp_attr) ->
      let* tp_list = List.map tp_list ~f in

      let+ constr = match constr with
        | Data (qi, variant_decls) ->
          let+ variant_decls = List.map variant_decls ~f:(fun variant_decl ->
            let+ variant_args = List.map variant_decl.variant_args ~f:(fun var_decl ->
              let+ var_type = f var_decl.var_type in
              { var_decl with
                var_type
              }
              )  in

            { variant_decl with variant_args }
          ) in

          Type.Data (qi, variant_decls)

        | _ -> return constr
      in
      Type.App (constr, tp_list, tp_attr)

  let rec fold ~(init : 'a) ~(f : 'a -> Type.t -> ('a, 'b) t_ext) tp_expr :
      ('a, 'b) t_ext =
    let open Syntax in
    match tp_expr with
    | Type.App (_constr, tp_list, _tp_attr) as typ ->
        let* acc = f typ init in
        List.fold_left tp_list
          ~f:(fun acc typ -> fold ~f ~init:acc typ)
          ~init:acc

  let rec rewrite_qual_idents ~f (tp_expr : Type.t) : (Type.t, 'a) t_ext =
    let open Syntax in
    match tp_expr with
    | App (Var id, [], tp_attr) -> return (Type.App (Var (f id), [], tp_attr))
    | App (AtomicToken qual_id, [], tp_attr) ->
        return (Type.App (AtomicToken (f qual_id), [], tp_attr))
    | App (Data (qual_id, variant_decls_list), [], tp_attr) ->
        let qual_id = f qual_id in
        let* variant_decls_list =
          List.map variant_decls_list ~f:(fun variant_decl ->
              let+ var_decls_list =
                List.map variant_decl.variant_args ~f:(fun var_decl ->
                    VarDecl.rewrite_types ~f:(rewrite_qual_idents ~f) var_decl)
              in

              { variant_decl with variant_args = var_decls_list })
        in
        return (Type.App (Data (qual_id, variant_decls_list), [], tp_attr))
    | _ -> descend ~f:(rewrite_qual_idents ~f) tp_expr
end

module Expr = struct
  let descend ~f (expr : Expr.t) : (Expr.t, 'a) t_ext =
    let open Syntax in
    match expr with
    | App (constr, expr_list, expr_attr) ->
        let+ expr_list = List.map expr_list ~f in
        Expr.App (constr, expr_list, expr_attr)
    | Binder (b, v_l, trgs, inner_expr, expr_attr) ->
        let+ _ = add_locals v_l
        and+ inner_expr = f inner_expr
        and+ trgs = List.map trgs ~f:(List.map ~f) in
        Expr.Binder (b, v_l, trgs, inner_expr, expr_attr)

  let rec rewrite_types ~(f : AstDef.Type.t -> (AstDef.Type.t, 'a) t_ext)
      (expr : Expr.t) : (Expr.t, 'a) t_ext =
    let open Syntax in
    match expr with
    | App (constr, expr_list, expr_attr) ->
        let* constr = match constr with
        | ExprExt expr_ext ->
          let* ext_hooks = current_ext_hooks in
          let+ expr_ext = ext_hooks.expr_ext_rewrite_types ~f expr_ext in

          Expr.ExprExt expr_ext
        | _ ->
          return constr
        in
        let+ expr_list = List.map expr_list ~f:(rewrite_types ~f)
        and+ expr_type = f expr_attr.expr_type in
        let expr_attr = { expr_attr with expr_type } in
        Expr.App (constr, expr_list, expr_attr)
    | Binder (b, var_decls, trgs, inner_expr, expr_attr) ->
        let* var_decls = List.map var_decls ~f:(VarDecl.rewrite_types ~f) in
        let+ _ = add_locals var_decls
        and+ inner_expr = rewrite_types ~f inner_expr
        and+ trgs =
          List.map trgs ~f:(fun exprs -> List.map exprs ~f:(rewrite_types ~f))
        in
        Expr.Binder (b, var_decls, trgs, inner_expr, expr_attr)

  let rec rewrite_qual_idents ~f (expr : Expr.t) : (Expr.t, 'a) t_ext =
    let open Syntax in
    match expr with
    | App (constr, expr_list, expr_attr) ->
        let+ expr_list = List.map expr_list ~f:(rewrite_qual_idents ~f)
        and+ expr_type = Type.rewrite_qual_idents ~f expr_attr.expr_type in
        let expr_attr = { expr_attr with expr_type } in
        let constr =
          match constr with
          | Var qual_ident -> Expr.Var (f qual_ident)
          | DataConstr qual_ident -> Expr.DataConstr (f qual_ident)
          | DataDestr qual_ident -> Expr.DataDestr (f qual_ident)
          | _ -> constr
        in
        Expr.App (constr, expr_list, expr_attr)
    | Binder (b, var_decls, trgs, inner_expr, expr_attr) ->
        let* var_decls =
          List.map var_decls
            ~f:(VarDecl.rewrite_types ~f:(Type.rewrite_qual_idents ~f))
        in
        let+ _ = add_locals var_decls
        and+ inner_expr = rewrite_qual_idents ~f inner_expr
        and+ trgs =
          List.map trgs ~f:(fun exprs ->
              List.map exprs ~f:(rewrite_qual_idents ~f))
        in

        Expr.Binder (b, var_decls, trgs, inner_expr, expr_attr)
end

module Stmt = struct
  let descend ~(f : Stmt.t -> (Stmt.t, 'a) t_ext) (stmt : Stmt.t) :
      (Stmt.t, 'a) t_ext =
    let open Syntax in
    match stmt.stmt_desc with
    | Block block_desc ->
        let* _ = enter_block block_desc in
        let* stmt_list = List.map block_desc.block_body ~f in
        let+ () = exit_block in
        {
          stmt with
          stmt_desc = Block { block_desc with block_body = stmt_list };
        }
    | Loop loop_desc ->
        let+ new_prebody = f loop_desc.loop_prebody
        and+ new_postbody = f loop_desc.loop_postbody in

        let loop_desc =
          {
            loop_desc with
            loop_prebody = new_prebody;
            loop_postbody = new_postbody;
          }
        in

        { stmt with stmt_desc = Loop loop_desc }
    | Cond cond_desc ->
        let+ new_then_branch = f cond_desc.cond_then
        and+ new_else_branch = f cond_desc.cond_else in

        let cond_desc =
          {
            cond_desc with
            cond_then = new_then_branch;
            cond_else = new_else_branch;
          }
        in

        { stmt with stmt_desc = Cond cond_desc }
    | _ -> return stmt

  let rewrite_expressions_top ~f ~c (stmt : Stmt.t) : (Stmt.t, 'a) t_ext =
    let open Syntax in
    match stmt.stmt_desc with
    | Basic basic_stmt -> (
        match basic_stmt with
        | VarDef var_def ->
            let+ new_init = Util.State.Option.map var_def.var_init ~f in
            {
              stmt with
              stmt_desc = Basic (VarDef { var_def with var_init = new_init });
            }
        | Spec (sk, spec) ->
            let+ new_spec_form = f spec.spec_form in
            {
              stmt with
              stmt_desc =
                Basic (Spec (sk, { spec with spec_form = new_spec_form }));
            }
        | Assign assign ->
            let+ assign_rhs = f assign.assign_rhs in
            {
              stmt with
              stmt_desc = Basic (Assign { assign with assign_rhs });
            }
        | Bind bind_desc ->
          let+ spec_form = f bind_desc.bind_rhs.spec_form in
          let bind_rhs = { bind_desc.bind_rhs with spec_form } in
          { stmt with stmt_desc = Basic (Bind { bind_desc with bind_rhs }) }
        | FieldRead field_read_desc ->
            let field_read_lhs = field_read_desc.field_read_lhs in
            let field_read_field = field_read_desc.field_read_field in
            let+ field_read_ref = f field_read_desc.field_read_ref in
            {
              stmt with
              stmt_desc =
                Basic
                  (FieldRead
                     { field_read_desc with field_read_lhs; field_read_field; field_read_ref });
            }
        | FieldWrite field_write_desc ->
            let* field_write_ref = f field_write_desc.field_write_ref in
            let+ field_write_val = f field_write_desc.field_write_val in
            {
              stmt with
              stmt_desc =
                Basic
                  (FieldWrite
                     { field_write_desc with field_write_ref; field_write_val });
            }
        | Return expr ->
            let+ expr = f expr in
            { stmt with stmt_desc = Basic (Return expr) }
        | Call call ->
            let+ call_args = List.map call.call_args ~f in
            { stmt with stmt_desc = Basic (Call { call with call_args }) }
        | Use use_desc ->
            let* use_args = List.map use_desc.use_args ~f in

            let+ use_witnesses_or_binds = match use_desc.use_kind with
            | Fold -> 
              List.map use_desc.use_witnesses_or_binds ~f:(fun (iden, expr) -> 
                let+ expr = f expr in
                (iden, expr)
              ) 
            | Unfold -> return use_desc.use_witnesses_or_binds
          
          in

            { stmt with stmt_desc = Basic (Use { use_desc with use_args; use_witnesses_or_binds }) }
        | New new_desc ->
            let+ new_args =
              List.map new_desc.new_args ~f:(fun (x, e_opt) ->
                  let+ e_opt = Option.map e_opt ~f in
                  (x, e_opt))
            in
            { stmt with stmt_desc = Basic (New { new_desc with new_args }) }
        | Fpu fpu_desc ->
            let* fpu_old_val = Option.map fpu_desc.fpu_old_val ~f in
            let+ fpu_new_val = f fpu_desc.fpu_new_val in
            {
              stmt with
              stmt_desc = Basic (Fpu { fpu_desc with fpu_old_val; fpu_new_val });
            }
        | StmtExt (stmt_ext, stmt_args) ->
          let+ stmt_args =
            List.map stmt_args ~f:(fun expr -> f expr) in
          { stmt with
            stmt_desc = Basic (StmtExt (stmt_ext, stmt_args))
          }
        (* TODO: add remaining *)
        | _ -> return stmt)
    | Loop loop_desc ->
        let+ new_contract =
          List.map loop_desc.loop_contract ~f:(fun contract ->
              let+ new_spec_form = f contract.spec_form in
              { contract with spec_form = new_spec_form })
        and+ new_contract_ext =
          let* ext_hooks = current_ext_hooks in
          List.map loop_desc.loop_contract_ext ~f:(ext_hooks.contract_ext_rewrite_exprs ~f)
        and+ new_prebody = c loop_desc.loop_prebody
        and+ new_test = f loop_desc.loop_test
        and+ new_postbody = c loop_desc.loop_postbody in
        {
          stmt with
          stmt_desc =
            Loop
              {
                loop_contract = new_contract;
                loop_contract_ext = new_contract_ext;
                loop_prebody = new_prebody;
                loop_test = new_test;
                loop_postbody = new_postbody;
              };
        }
    | Cond cond_desc ->
        let+ new_test = Option.map ~f cond_desc.cond_test
        and+ new_then_branch = c cond_desc.cond_then
        and+ new_else_branch = c cond_desc.cond_else in

        {
          stmt with
          stmt_desc =
            Cond
              {
                cond_desc with
                cond_test = new_test;
                cond_then = new_then_branch;
                cond_else = new_else_branch;
              };
        }
    | _ -> descend stmt ~f:c

  let rec rewrite_expressions ~f stmt : (Stmt.t, 'a) t_ext =
    rewrite_expressions_top ~f ~c:(rewrite_expressions ~f) stmt

  let rec rewrite_types ~f stmt : (Stmt.t, 'a) t_ext =
    let open Syntax in
    match stmt.Stmt.stmt_desc with
    | Stmt.Basic (VarDef var_def) ->
        let* var_decl = VarDecl.rewrite_types ~f var_def.var_decl
        and* new_init =
          Option.map var_def.var_init ~f:(Expr.rewrite_types ~f)
        in
        let+ _ = add_locals [ var_decl ] in
        {
          stmt with
          stmt_desc = Basic (VarDef { var_decl; var_init = new_init; var_is_free = var_def.var_is_free });
        }
    | Stmt.Basic (StmtExt (stmt_ext, stmt_args)) ->
      let* ext_hooks = current_ext_hooks in
      let* stmt_ext = ext_hooks.stmt_ext_rewrite_types ~f stmt_ext in

      let stmt = { stmt with stmt_desc = Basic (StmtExt (stmt_ext, stmt_args)) } in
        rewrite_expressions_top ~f:(Expr.rewrite_types ~f) ~c:(rewrite_types ~f)
          stmt
    | _ ->
        rewrite_expressions_top ~f:(Expr.rewrite_types ~f) ~c:(rewrite_types ~f)
          stmt

  let rec rewrite_qual_idents ~f stmt : (Stmt.t, 'a) t_ext =
    let open Syntax in
    match stmt.Stmt.stmt_desc with
    | Basic basic_stmt -> (
        match basic_stmt with
        | VarDef var_def ->
            let+ var_decl =
              VarDecl.rewrite_types
                ~f:(Type.rewrite_qual_idents ~f)
                var_def.var_decl
            and+ var_init =
              Option.map var_def.var_init ~f:(Expr.rewrite_qual_idents ~f)
            in
            { stmt with stmt_desc = Basic (VarDef { var_decl; var_init; var_is_free = var_def.var_is_free }) }
        | Assign assign ->
            let+ assign_rhs = Expr.rewrite_qual_idents ~f assign.assign_rhs in
            let assign_lhs = Base.List.map assign.assign_lhs ~f in
            {
              stmt with
              stmt_desc = Basic (Assign { assign with assign_lhs; assign_rhs });
            }
        | Bind bind_desc ->
            let bind_lhs = Base.List.map bind_desc.bind_lhs ~f in
            let+ spec_form = Expr.rewrite_qual_idents ~f bind_desc.bind_rhs.spec_form in
            let bind_rhs = { bind_desc.bind_rhs with spec_form } in
            { stmt with stmt_desc = Basic (Bind { bind_lhs; bind_rhs }) }
        | FieldRead field_read_desc ->
            let field_read_lhs = f field_read_desc.field_read_lhs in
            let field_read_field = f field_read_desc.field_read_field in
            let+ field_read_ref =
              Expr.rewrite_qual_idents ~f field_read_desc.field_read_ref
            in
            {
              stmt with
              stmt_desc =
                Basic
                  (FieldRead
                     { field_read_desc with field_read_lhs; field_read_field; field_read_ref });
            }
        | FieldWrite field_write_desc ->
          let* field_write_val =
            Expr.rewrite_qual_idents ~f field_write_desc.field_write_val
          in
          let field_write_field = f field_write_desc.field_write_field in
          let+ field_write_ref =
            Expr.rewrite_qual_idents ~f field_write_desc.field_write_ref
          in
          { stmt with
            stmt_desc =
              Basic
                (FieldWrite
                   { field_write_ref; field_write_field; field_write_val });
          }
        | Return expr ->
            let+ expr = Expr.rewrite_qual_idents ~f expr in
            { stmt with stmt_desc = Basic (Return expr) }
        | Call call ->
            let+ call_args =
              List.map call.call_args ~f:(Expr.rewrite_qual_idents ~f)
            in
            let call_lhs = Base.List.map call.call_lhs ~f in
            let call_name = f call.call_name in
            {
              stmt with
              stmt_desc = Basic (Call { call with call_lhs; call_name; call_args });
            }
        | Use use_desc ->
            let use_name = f use_desc.use_name in

            let* use_args =
              List.map use_desc.use_args ~f:(Expr.rewrite_qual_idents ~f)
            in
            let+ use_witnesses_or_binds =  
              match use_desc.use_kind with
              | Fold ->
                List.map use_desc.use_witnesses_or_binds ~f:(fun (i, e) -> 
                    let+ e = Expr.rewrite_qual_idents ~f e in
                    (i, e))
              | Unfold ->
                return @@ Base.List.map use_desc.use_witnesses_or_binds ~f:(fun (i, e) -> 
                    let i = QualIdent.to_ident (f (QualIdent.from_ident i)) in
                    (i, e)
                  )
            in
            
            {
              stmt with
              stmt_desc = Basic (Use { 
                  use_desc with 
                  use_name; use_args; use_witnesses_or_binds
              });
            }
        | New new_desc ->
            let new_lhs = f new_desc.new_lhs in
            let+ new_args =
              List.map new_desc.new_args ~f:(fun (x, e_opt) ->
                  let+ e_opt =
                    Option.map e_opt ~f:(Expr.rewrite_qual_idents ~f)
                  in
                  (f x, e_opt))
            in
            { stmt with stmt_desc = Basic (New { new_lhs; new_args }) }
        | Fpu fpu_desc ->
            let fpu_field = f fpu_desc.fpu_field in
            let+ fpu_ref = Expr.rewrite_qual_idents ~f fpu_desc.fpu_ref
            and+ fpu_old_val =
              Option.map fpu_desc.fpu_old_val ~f:(Expr.rewrite_qual_idents ~f)
            and+ fpu_new_val =
              Expr.rewrite_qual_idents ~f fpu_desc.fpu_new_val
            in
            {
              stmt with
              stmt_desc =
                Basic (Fpu { fpu_ref; fpu_field; fpu_old_val; fpu_new_val });
            }
        | Havoc hvc ->
            let havoc_var = f hvc.havoc_var in
            return { stmt with stmt_desc = Basic (Havoc { hvc with havoc_var }) }
        (* TODO: add remaining *)
        | _ ->
            rewrite_expressions_top
              ~f:(Expr.rewrite_qual_idents ~f)
              ~c:(rewrite_qual_idents ~f) stmt)
    | _ ->
        rewrite_expressions_top
          ~f:(Expr.rewrite_qual_idents ~f)
          ~c:(rewrite_qual_idents ~f) stmt
end

module Callable = struct
  let rewrite_expressions_top ~(fe : expr -> (expr, 'a) t_ext) ~fs callable :
      (Callable.t, 'a) t_ext =
    let open Syntax in
    let open AstDef.Stmt in
    let rewrite_specs specs =
      List.map specs ~f:(fun spec ->
          let+ new_spec_form = fe spec.spec_form in
          { spec with spec_form = new_spec_form })
    in
    let call_decl = Callable.to_decl callable in
    (* [call_decl_contract_ext] is left as-is here, same as [stmt_ext] in the proc body
       below -- neither extension point is substituted during this generic rewrite
       (used for e.g. module-instantiation substitution), a pre-existing gap this
       doesn't attempt to close. *)
    let* _ = add_call_decl_locals call_decl
    and* new_preconds = rewrite_specs call_decl.call_decl_precond
    and* new_postconds = rewrite_specs call_decl.call_decl_postcond in
    let call_decl =
      {
        call_decl with
        call_decl_precond = new_preconds;
        call_decl_postcond = new_postconds;
      }
    in
    match callable.call_def with
    | Callable.FuncDef { func_body } ->
        let+ func_body = Option.map func_body ~f:fe in
        Callable.{ call_decl; call_def = Callable.FuncDef { func_body } }
    | Callable.ProcDef { proc_body } ->
        (* Logs.debug (fun m -> m "Rewriter.Callable.rewrite_expressions_top: old_proc_body = %a" (Print.pr_option AstDef.Stmt.pr) proc_body); *)
        let+ proc_body = Option.map proc_body ~f:fs in
        (* Logs.debug (fun m -> m "Rewriter.Callable.rewrite_expressions_top: new_proc_body = %a" (Print.pr_option AstDef.Stmt.pr) proc_body); *)
        Callable.{ call_decl; call_def = Callable.ProcDef { proc_body } }

  let rewrite_scoped ~f callable =
    let open Syntax in
    (*Logs.debug (fun m ->
        m "Rewriter.Callable.rewrite_scoped: callable = %a" Callable.pr callable);*)

    (* rewrite_scoped assumes the callable will always be opened BEFORE any Callable.rewrite_ call.
       This is ensured in all the Module.rewrite_ methods.

       Therefore, no need to call enter_callable or exit_callable here.
    *)
    (*Logs.debug (fun m -> m "Rewriter.Callable.rewrite_scoped: entered callable");*)
    let* callable = f callable in

    return callable

  let rewrite_expressions ~f callable =
    rewrite_scoped
      ~f:(rewrite_expressions_top ~fe:f ~fs:(Stmt.rewrite_expressions ~f))
      callable

  let rewrite_types_top ~(ft : type_expr -> type_expr t) ~fe ~fs callable :
      (Callable.t, 'a) t_ext =
    let open Syntax in
    let call_decl = Callable.to_decl callable in
    let* call_decl_formals =
      List.map call_decl.call_decl_formals ~f:(VarDecl.rewrite_types ~f:ft)
    and* call_decl_returns =
      List.map call_decl.call_decl_returns ~f:(VarDecl.rewrite_types ~f:ft)
    and* call_decl_locals =
      List.map call_decl.call_decl_locals ~f:(VarDecl.rewrite_types ~f:ft)
    in
    let call_decl =
      { call_decl with call_decl_formals; call_decl_returns; call_decl_locals }
    in
    let callable = { callable with call_decl } in
    rewrite_expressions_top ~fe ~fs callable

  let rewrite_types ~f callable =
    rewrite_scoped
      ~f:
        (rewrite_types_top ~ft:f ~fe:(Expr.rewrite_types ~f)
           ~fs:(Stmt.rewrite_types ~f))
      callable

  let rewrite_stmts ~f callable =
    let id_expr_rewriter e = return e in

    rewrite_scoped
      ~f:(rewrite_expressions_top ~fe:id_expr_rewriter ~fs:f)
      callable

  let rewrite_qual_idents ~f callable =
    let open Syntax in
    let* callable =
      rewrite_scoped
        ~f:
          (rewrite_types_top
             ~ft:(Type.rewrite_qual_idents ~f)
             ~fe:(Expr.rewrite_qual_idents ~f)
             ~fs:(Stmt.rewrite_qual_idents ~f))
        callable
    in

    (* [f] (a QualIdent substitution, e.g. from module/functor instantiation)
       isn't guaranteed injective on mask entries -- two formerly-distinct
       entries could collapse into the same one, which would otherwise
       persist as an un-deduped duplicate (see [Callable.mask_canon]); both
       [call_decl_needs_mask] and [call_decl_grants_mask] need the same rewrite. *)
    let rewrite_mask mask =
      let+ mask =
        List.map mask ~f:(fun (qi, args) ->
            let+ args = List.map args ~f:(Expr.rewrite_qual_idents ~f) in
            (f qi, args))
      in
      Callable.mask_canon mask
    in
    let* call_decl_needs_mask =
      match callable.call_decl.call_decl_needs_mask with
      | None -> return None
      | Some mask ->
          let+ mask = rewrite_mask mask in
          Some mask
    in
    let* call_decl_grants_mask =
      match callable.call_decl.call_decl_grants_mask with
      | None -> return None
      | Some mask ->
          let+ mask = rewrite_mask mask in
          Some mask
    in
    let callable =
      {
        callable with
        call_decl = { callable.call_decl with call_decl_needs_mask; call_decl_grants_mask };
      }
    in
    return callable
end

module Module = struct
  let rec rewrite_symbols ~f (mdef : Module.t) : (Module.t, 'a) t_ext =
    let open Module in
    let open Syntax in
    let* _ = enter_module mdef
    and* symbols =
      List.map mdef.mod_def ~f:(function
        | SymbolDef symbol ->
            (* Logs.debug (fun m -> m "Rewriter.Module.rewrite_symbols: old_symbol: %a" AstDef.Symbol.pr symbol); *)
            let* symbol_def = f symbol in
            let* _ = set_symbol symbol_def in

            (* Logs.debug (fun m -> m "Rewriter.Module.rewrite_symbols: new_symbol: %a" AstDef.Symbol.pr symbol); *)
            let* tbl = get_table in

            (* Logs.debug (fun m -> m "Rewriter.Module.rewrite_symbols: SymbolTbl Symbols: \n%a\n" (Util.Print.pr_list_comma (fun ppf (k,v) -> Stdlib.Format.fprintf ppf "%a -> %a" QualIdent.pr k Module.pr_symbol v)) (Map.to_alist (Map.filter_keys tbl.tbl_symbols ~f:(fun k -> Poly.((QualIdent.to_string k) = "$Program.pr"))))); *)
            return (SymbolDef symbol_def)
        | import -> return import)
    in
    let mdef = { mdef with mod_def = symbols } in
    exit_module mdef

  let rec rec_rewrite_symbols ~f (mdef : Module.t) : (Module.t, 'a) t_ext =
    let open Module in
    let open Syntax in
    let* _ = enter_module mdef
    and* symbols =
      List.map mdef.mod_def ~f:(function
        | SymbolDef symbol ->
            let* symbol_def =
              match symbol with
              | ModDef mod_def ->
                  let* new_mod_def = rec_rewrite_symbols ~f mod_def in
                  return @@ ModDef new_mod_def
              | _ -> return symbol
            in

            (* Logs.debug (fun m -> m "Rewriter.Module.rewrite_symbols: old_symbol: %a" AstDef.Symbol.pr symbol); *)
            let+ symbol_def = f symbol_def and+ _ = set_symbol symbol_def in
            (* Logs.debug (fun m -> m "Rewriter.Module.rewrite_symbols: new_symbol: %a" AstDef.Symbol.pr symbol); *)
            SymbolDef symbol_def
        | import -> return import)
    in
    let mdef = { mdef with mod_def = symbols } in
    exit_module mdef

  let rec rewrite_expressions ~f mdef : (Module.t, 'a) t_ext =
    let open Syntax in
    let open Module in
    let rewrite_symbol = function
      | VarDef var_def ->
          let+ new_var_init = Option.map var_def.var_init ~f in
          VarDef { var_def with var_init = new_var_init }
      | CallDef call_def ->
          let* _ = enter_callable call_def in

          let* new_call_def = Callable.rewrite_expressions ~f call_def in
          let+ new_call_def = exit_callable new_call_def in

          CallDef new_call_def
      | ModDef mod_def ->
          let+ new_mod_def = rewrite_expressions ~f mod_def in
          ModDef new_mod_def
      | mem_def -> return mem_def
    in
    rewrite_symbols ~f:rewrite_symbol mdef

  let rec rewrite_stmts ~f mdef : (Module.t, 'a) t_ext =
    let open Syntax in
    let open Module in
    let rewrite_symbol = function
      | CallDef call_def ->
          let* _ = enter_callable call_def in

          let* new_call_def = Callable.rewrite_stmts ~f call_def in
          let+ new_call_def = exit_callable new_call_def in

          CallDef new_call_def
      | ModDef mod_def ->
          let+ new_mod_def = rewrite_stmts ~f mod_def in
          ModDef new_mod_def
      | mem_def -> return mem_def
    in
    rewrite_symbols ~f:rewrite_symbol mdef

  let rec rewrite_types ~f mdef : (Module.t, 'a) t_ext =
    let open Syntax in
    let rewrite_symbol : Module.symbol -> Module.symbol t =
      let open Module in
      function
      | TypeDef type_def ->
          let+ type_def_expr = Option.map type_def.type_def_expr ~f in
          TypeDef { type_def with type_def_expr }
      | ConstrDef constr_def ->
          let+ constr_args =
            List.map constr_def.constr_args ~f:(VarDecl.rewrite_types ~f)
          and+ constr_return_type = f constr_def.constr_return_type in
          ConstrDef { constr_def with constr_args; constr_return_type }
      | DestrDef destr_def ->
          let+ destr_arg = f destr_def.destr_arg
          and+ destr_return_type = f destr_def.destr_return_type in
          DestrDef { destr_def with destr_arg; destr_return_type }
      | VarDef var_def ->
          let+ var_decl = VarDecl.rewrite_types ~f var_def.var_decl
          and+ var_init =
            Option.map var_def.var_init ~f:(Expr.rewrite_types ~f)
          in
          VarDef { var_decl; var_init; var_is_free = var_def.var_is_free }
      | FieldDef field_def ->
          let+ field_type = f field_def.field_type in
          FieldDef { field_def with field_type }
      | CallDef call_def ->
          let* _ = enter_callable call_def in

          let* new_call_def = Callable.rewrite_types ~f call_def in
          let+ new_call_def = exit_callable new_call_def in

          CallDef new_call_def
      | ModDef mod_def ->
          let+ new_mod_def = rewrite_types ~f mod_def in
          ModDef new_mod_def
      | mem_def -> return mem_def
    in
    rewrite_symbols ~f:rewrite_symbol mdef

  let rec rewrite_callables ~f mdef : (Module.t, 'a) t_ext =
    let open Syntax in
    let rewrite_symbol =
      let open Module in
      function
      | CallDef call_def ->
          let* _ = enter_callable call_def in

          let* new_call_def = f call_def in
          let+ new_call_def = exit_callable new_call_def in
          (* Logs.debug (fun m -> m "Rewriter.Module.rewrite_callables: new_call_def = %a" AstDef.Callable.pr new_call_def); *)
          CallDef new_call_def
      | ModDef mod_def ->
          let+ new_mod_def = rewrite_callables ~f mod_def in

          (* Logs.debug (fun m -> m "Rewriter.Module.rewrite_callables: new_module_def = %a" AstDef.Module.pr new_mod_def); *)
          ModDef new_mod_def
      | mem_def -> return mem_def
    in
    rewrite_symbols ~f:rewrite_symbol mdef

  let rec rewrite_qual_idents_in_symbol ~(f : QualIdent.t -> QualIdent.t) :
      Module.symbol -> (Module.symbol, 'a) t_ext =
    let open Syntax in
    let open Module in
    function
    | ModInst mod_inst ->
        let+ mod_inst_def =
          Option.map mod_inst.mod_inst_def
            ~f:(fun (mod_inst_def_funct, mod_inst_def_args) ->
              let+ mod_inst_def_args =
                List.map mod_inst_def_args ~f:(function
                  | Module.ModArg qi -> return (Module.ModArg (f qi))
                  | Module.TypeArg tp ->
                      let+ tp = Type.rewrite_qual_idents ~f tp in
                      Module.TypeArg tp)
              in
              (f mod_inst_def_funct, mod_inst_def_args))
        in
        let mod_inst_type = f mod_inst.mod_inst_type in
        ModInst { mod_inst with mod_inst_type; mod_inst_def }
    | TypeDef type_def ->
        let+ type_def_expr =
          Option.map type_def.type_def_expr ~f:(Type.rewrite_qual_idents ~f)
        in
        TypeDef { type_def with type_def_expr }
    | ConstrDef constr_def ->
        let+ constr_args =
          List.map constr_def.constr_args
            ~f:(VarDecl.rewrite_types ~f:(Type.rewrite_qual_idents ~f))
        and+ constr_return_type =
          Type.rewrite_qual_idents ~f constr_def.constr_return_type
        in
        ConstrDef { constr_def with constr_args; constr_return_type }
    | DestrDef destr_def ->
        let+ destr_arg = Type.rewrite_qual_idents ~f destr_def.destr_arg
        and+ destr_return_type =
          Type.rewrite_qual_idents ~f destr_def.destr_return_type
        in
        DestrDef { destr_def with destr_arg; destr_return_type }
    | VarDef var_def ->
        let+ var_decl =
          VarDecl.rewrite_types
            ~f:(Type.rewrite_qual_idents ~f)
            var_def.var_decl
        and+ var_init =
          Option.map var_def.var_init ~f:(Expr.rewrite_qual_idents ~f)
        in
        VarDef { var_decl; var_init; var_is_free = var_def.var_is_free }
    | FieldDef field_def ->
        let+ field_type = Type.rewrite_qual_idents ~f field_def.field_type in
        FieldDef { field_def with field_type }
    | CallDef call_def ->
        let* _ = enter_callable call_def in

        let* new_call_def = Callable.rewrite_qual_idents ~f call_def in
        let+ new_call_def = exit_callable new_call_def in

        CallDef new_call_def
    | ModDef mod_def ->
        let+ new_mod_def = rewrite_qual_idents ~f mod_def in
        ModDef new_mod_def

  and rewrite_qual_idents ~f mdef : (Module.t, 'a) t_ext =
    (* TODO: rewrite imports *)
    let open Syntax in
    let open Module in
    let+ mdef1 = rewrite_symbols ~f:(rewrite_qual_idents_in_symbol ~f) mdef in
    let mod_decl_interfaces =
      Set.fold mdef1.mod_decl.mod_decl_interfaces
        ~init:(Set.empty (module QualIdent))
        ~f:(fun interfaces id -> Set.add interfaces (f id))
    in
    let mod_decl_returns = Base.Option.map ~f mdef1.mod_decl.mod_decl_returns in
    let mod_decl =
      { mdef1.mod_decl with mod_decl_interfaces; mod_decl_returns }
    in
    { mdef1 with mod_decl }
end

module Symbol = struct
  let reify (name, symbol, subst) =
    (*Logs.debug (fun m ->
        m "Rewriter.Symbol.reify %a; %a" AstDef.Symbol.pr symbol
          (Print.pr_list_comma (fun ppf (q, i_l) ->
               Stdlib.Format.fprintf ppf "%a -> %a" QualIdent.pr q
                 (Print.pr_list_comma Ident.pr)
                 i_l))
          subst);*)

    match SymbolTbl.qid_subst subst with
    | [] -> return symbol
    | _ ->
        let open Syntax in
        let+ tbl = get_table in
        let tbl_scope = SymbolTbl.goto name tbl in
        let symbol0 = match symbol with
          | AstDef.Module.ModDef mod_def ->
            let mod_decl =
              { mod_def.mod_decl with
                mod_decl_formals = if SymbolTbl.is_instance subst then [] else mod_def.mod_decl.mod_decl_formals;
                mod_decl_is_interface = SymbolTbl.is_abstract subst
              } in
            AstDef.Module.ModDef { mod_def with mod_decl }
          | _ -> symbol
        in
        let _, symbol1 =
          eval
            (Module.rewrite_qual_idents_in_symbol
               ~f:(subst |> SymbolTbl.qid_subst |> QualIdent.requalify)
               symbol0)
            tbl_scope
        in

        (* Logs.debug (fun m -> m "Rewriter.Symbol.reify: Reified symbol = %a" AstDef.Symbol.pr symbol1); *)
        match symbol1 with
        | CallDef call_def -> AstDef.Module.CallDef (AstDef.Callable.set_machine_free call_def)
        | _ -> symbol1

  let reify_type_def loc (name, symbol, subst) :
      (AstDef.Type.t Base.Option.t, 'a) t_ext =
    let open Syntax in
    match symbol with
    | AstDef.Module.TypeDef { type_def_expr = None; _ } -> return None
    | TypeDef { type_def_expr = Some tp_expr; _ } ->
        let+ tp_expr =
          Type.rewrite_qual_idents ~f:(subst |> SymbolTbl.qid_subst |> QualIdent.requalify) tp_expr
        in
        Some tp_expr
    | ModDef { mod_decl = { mod_decl_rep = Some rep_id; _ }; _ } ->
        let+ tp_expr =
          AstDef.Type.mk_var (QualIdent.append name rep_id)
          |> Type.rewrite_qual_idents ~f:(subst |> SymbolTbl.qid_subst |> QualIdent.requalify)
        in
        Some tp_expr
    | _ -> Error.error loc "Expected type identifier"

  let reify_type loc (_name, symbol, subst) : (AstDef.Type.t, 'a) t_ext =
    let tp_expr =
      match symbol with
      | AstDef.Module.VarDef { var_decl; _ } -> var_decl.var_type
      | FieldDef field_def -> field_def.field_type
      | _ -> Error.error loc "Expected expression identifier"
    in
    Type.rewrite_qual_idents ~f:(subst |> SymbolTbl.qid_subst |> QualIdent.requalify) tp_expr

  let reify_field_type loc (_name, symbol, subst) : (AstDef.Type.t, 'a) t_ext =
    let tp_expr =
      match symbol with
      | AstDef.Module.FieldDef { field_type = App (Fld, [ tp ], _); _ } -> tp
      | _ -> Error.error loc "Expected field identifier"
    in
    Type.rewrite_qual_idents ~f:(subst |> SymbolTbl.qid_subst |> QualIdent.requalify) tp_expr

  let orig_symbol (_name, symbol, _subst) = symbol
  let orig_qid (name, _symbol, _subst) = name
  let subst (_name, _symbol, subst) = SymbolTbl.qid_subst subst
  let extract (_name, symbol, subst) ~f = f (SymbolTbl.is_instance subst) (subst |> SymbolTbl.qid_subst |> QualIdent.requalify) symbol
  let extend_subst s (name, symbol, subst) = (name, symbol, SymbolTbl.extend_subst s subst)
  let is_instance (_, _, subst) = SymbolTbl.is_instance subst
  
  type t = QualIdent.t * AstDef.Module.symbol * SymbolTbl.subst

  let pr ppf (name, symbol, subst) =
    Stdlib.Format.fprintf ppf "%a -> %a [%a]" QualIdent.pr name AstDef.Symbol.pr
      symbol
      (Print.pr_list_comma (fun ppf (q, i_l) ->
           Stdlib.Format.fprintf ppf "%a -> %a" QualIdent.pr q
             (Print.pr_list_comma Ident.pr)
             i_l))
      subst
end

let resolve_and_find_opt name: ((QualIdent.t * Symbol.t) option, 'a) t_ext =
  let open Syntax in
  let* tbl = get_table in

  match SymbolTbl.resolve_and_find name tbl with
  | Some (alias_qual_ident, qual_ident, symbol, subst) ->
    return (Some (qual_ident, (alias_qual_ident, symbol, subst)))
  | None ->
    (* Last resort for a machine-free symbol's already-validated contract/body: a prior
       qualident substitution (e.g. a functor formal rewritten to its argument) can
       produce an absolute reference that no longer carries the instantiation context
       that made it legal, so the scope-relative guard above rejects it here even
       though it already resolved once. Only reached after that guard has failed, so
       it can't change the outcome for anything that resolves normally. *)
    let* relaxed = is_relaxed_lookup in
    if not relaxed then return None
    else
      let+ symbol = find_absolute name in
      Base.Option.map symbol ~f:(fun symbol -> (name, (name, symbol, (false, false, []))))

let resolve_and_find name : (QualIdent.t * Symbol.t, 'a) t_ext =
  let open Syntax in
  let+ resolved = resolve_and_find_opt name in
  match resolved with
  | Some resolved -> resolved
  | None -> SymbolTbl.unknown_ident_error (QualIdent.to_loc name) name

let resolve name : (QualIdent.t, 'a) t_ext =
  let open Syntax in
  let+ qual_ident, _ = resolve_and_find name in
  (*Logs.debug (fun m ->
      m "Rewriter.resolve: name = %a; qual_ident = %a" QualIdent.pr name
        QualIdent.pr qual_ident);*)
  qual_ident

let resolve_opt name : (QualIdent.t option, 'a) t_ext =
  let open Syntax in
  let+ result = resolve_and_find_opt name in

  result |> Base.Option.map ~f:(fun (qual_ident, _) -> qual_ident)

let find name : (Symbol.t, 'a) t_ext =
  let open Syntax in
  let+ _, symbol = resolve_and_find name in
  symbol


let find_and_reify name : (AstDef.Module.symbol, 'a) t_ext =
  let open Syntax in
  let* symbol = find name in
  (*Logs.debug (fun m ->
      m "Rewriter.find_and_reify: symbol = %a" Symbol.pr symbol);*)
  Symbol.reify symbol

let find_and_reify_var name : (AstDef.Stmt.var_def, 'a) t_ext =
  let open Syntax in
  let+ symbol = find_and_reify name in
  match symbol with
  | VarDef var_def -> var_def
  | _ -> Error.type_error (QualIdent.to_loc name) (Printf.sprintf "Expected var or val but found %s" (AstDef.Symbol.kind symbol))

let find_and_reify_callable name : (AstDef.Callable.t, 'a) t_ext =
  let open Syntax in
  let+ symbol = find_and_reify name in
  match symbol with
  | CallDef call_def -> call_def
  | _ -> Error.type_error (QualIdent.to_loc name) (Printf.sprintf "Expected callable but found %s" (AstDef.Symbol.kind symbol))

let find_and_reify_field name : (AstDef.Module.field_def, 'a) t_ext =
  let open Syntax in
  let+ symbol = find_and_reify name in
  match symbol with
  | FieldDef field -> field
  | _ -> Error.type_error (QualIdent.to_loc name) (Printf.sprintf "Expected field but found %s" (AstDef.Symbol.kind symbol))

let find_and_reify_module name : (AstDef.Module.t, 'a) t_ext =
  let open Syntax in
  let+ symbol = find_and_reify name in
  match symbol with
  | ModDef m -> m
  | _ -> Error.type_error (QualIdent.to_loc name) (Printf.sprintf "Expected module or interface but found %s" (AstDef.Symbol.kind symbol))


let is_local qual_ident s =
  let s, qual_ident = resolve qual_ident s in
  (s, Base.List.is_empty qual_ident.qual_path)



