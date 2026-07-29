open Ast

(* These callback-bundle types are defined in Ast.Rewriter (alongside the [ext_hooks]
   type they populate) rather than here, because Rewriter's state needs to know their
   shape without depending on lib/ext. The aliases below keep this module's existing
   names -- and every extension's [type_check_*] signatures -- unchanged. *)

(** Set of functions from Typing.ml available for type checking `Type.type_ext`  *)
type type_check_type_expr_functs = Rewriter.type_check_type_expr_functs = {
  process_type_expr : type_expr -> type_expr Rewriter.t;
}

(** Set of functions from Typing.ml available for type checking `Expr.expr_ext`  *)
type type_check_expr_functs = Rewriter.type_check_expr_functs = {
  check_and_set : expr -> type_expr -> type_expr -> type_expr -> expr Rewriter.t;
  process_expr : expr -> type_expr -> expr Rewriter.t;
  type_mismatch_error : 'a. location -> type_expr -> type_expr -> 'a;
  expand_type_expr : type_expr -> (type_expr, unit) Ast__Rewriter.t_ext;
}

(** Set of functions from Typing.ml available for type checking `Stmt.stmt_ext`  *)
type type_check_stmt_functs = Rewriter.type_check_stmt_functs = {
  get_assign_lhs :  is_init:bool ->
                    ?is_ghost_cmd:bool ->
                    qual_ident ->
                    unit Rewriter.state ->
                    unit Rewriter.state * (qual_ident * var_decl);

  expand_type_expr : type_expr -> (type_expr, unit) Ast__Rewriter.t_ext;

  disambiguate_process_expr : expr -> type_expr -> ProgUtils.DisambiguationTbl.t -> expr Rewriter.t;

  type_mismatch_error : 'a. location -> type_expr -> type_expr -> 'a;

  disam_tbl_add_var_decl : var_decl -> ProgUtils.DisambiguationTbl.t -> var_decl * ProgUtils.DisambiguationTbl.t;

  process_symbol : Module.symbol -> Module.symbol Rewriter.t;

  process_stmt : Callable.call_decl -> Stmt.t -> ProgUtils.DisambiguationTbl.t -> (Stmt.t * ProgUtils.DisambiguationTbl.t) Rewriter.t;
}

(* Main Extension API *)
module type Ext = sig
  (* Config *)
  val lib_source : (string * string) option

  (* AstDef *)
  val type_ext_to_name : (Type.type_ext -> string)

  val expr_ext_to_string : (Expr.expr_ext -> string)

  val pr_basic_stmt_ext : Stdlib.Format.formatter -> Stmt.stmt_ext -> expr list -> unit
  val contract_ext_to_string : Stmt.contract_ext -> string

  val basic_stmt_ext_symbols: Stmt.stmt_ext -> QualIdentSet.t
  val basic_stmt_ext_local_vars_modified : Stmt.stmt_ext -> expr list -> ident list
  val basic_stmt_ext_fields_accessed : Stmt.stmt_ext -> expr list -> qual_ident list

  (** The [stmt_desc]-level sibling of the [pr_basic_stmt_ext]/[basic_stmt_ext_*]
      family above, for the self-contained [Stmt.StmtExt] extension point (statements
      that need a nested [Stmt.t] of their own -- see
      [Stmt.basic_stmt_desc.BasicStmtExt]'s doc comment). *)
  val pr_stmt_ext : Stdlib.Format.formatter -> Stmt.stmt_ext -> unit
  val stmt_ext_symbols : Stmt.stmt_ext -> QualIdentSet.t
  val stmt_ext_local_vars_modified : Stmt.stmt_ext -> ident list
  val stmt_ext_fields_accessed : Stmt.stmt_ext -> qual_ident list

  (** Whether *this extension itself* (not [Cont]) declares the given constructor --
      not "does this chain recognize it" (that's what chaining to [Cont] in the
      wildcard case already gives every other hook here). Used solely so
      [lib/ext/ext.ml] can build a "did you mean `--extension X`" suggestion when the
      active chain's [type_check_*]/etc. hits its terminal [DefaultExt] case: it tries
      every *other* known `--extension` chain's [type_ext_is_recognized] & co. against
      the same value, and if exactly one recognizes it, names that flag in the error
      instead of a bare "no active extension recognizes this". Implement by matching
      only your own constructors (`true`) and deferring everything else to [Cont]. *)
  val type_ext_is_recognized : Type.type_ext -> bool
  val expr_ext_is_recognized : Expr.expr_ext -> bool
  val stmt_ext_is_recognized : Stmt.stmt_ext -> bool
  val contract_ext_is_recognized : Stmt.contract_ext -> bool


  (* Rewriter *)
  val expr_ext_rewrite_types :
    f:(type_expr -> type_expr Rewriter.t)
    -> Expr.expr_ext
    -> Expr.expr_ext Rewriter.t

  val basic_stmt_ext_rewrite_types :
    f: (type_expr -> type_expr Rewriter.t)
    -> Stmt.stmt_ext
    -> Stmt.stmt_ext Rewriter.t

  (** Generic substitution for the top-level [Stmt.StmtExt] extension point: applies
      [f] to every expression and [c] to every nested [Stmt.t] a [stmt_ext] value
      carries. *)
  val stmt_ext_rewrite :
    f:(expr -> expr Rewriter.t)
    -> c:(Stmt.t -> Stmt.t Rewriter.t)
    -> Stmt.stmt_ext
    -> Stmt.stmt_ext Rewriter.t

  (** Applies [f] to every expression a [contract_ext] value carries (e.g. each
      measure's [spec_form] for `decreases`). Used for generic substitution during
      things like module instantiation, the same reason [basic_stmt_ext_rewrite_types]
      exists for types -- core code needs to rewrite every expression in a callable's
      contract uniformly without knowing what a given [contract_ext] means. *)
  val contract_ext_rewrite_exprs :
    f:(expr -> expr Rewriter.t)
    -> Stmt.contract_ext
    -> Stmt.contract_ext Rewriter.t


  (* Typing *)
  val type_check_type_expr : Type.type_ext -> type_expr list -> Type.type_attr -> type_check_type_expr_functs -> type_expr Rewriter.t

  val type_check_expr : Expr.expr_ext -> expr list -> Expr.expr_attr -> type_expr -> type_check_expr_functs -> expr Rewriter.t

  val type_check_basic_stmt :
    Callable.call_decl ->
    Stmt.stmt_ext -> expr list ->
    location ->
    ProgUtils.DisambiguationTbl.t ->
    type_check_stmt_functs ->
    (Stmt.basic_stmt_desc * ProgUtils.DisambiguationTbl.t) Rewriter.t

  (** The [stmt_desc]-level sibling of [type_check_basic_stmt], for the self-contained
      [Stmt.StmtExt] extension point. Returns a whole [Stmt.stmt_desc] (typically
      another [StmtExt], left for [rewrite_stmt_ext] to lower once type-checking has
      run -- e.g. a purity check on an asserted fact) rather than a [basic_stmt_desc],
      since it isn't constrained to stay "basic". *)
  val type_check_stmt_ext :
    Callable.call_decl ->
    Stmt.stmt_ext ->
    location ->
    ProgUtils.DisambiguationTbl.t ->
    type_check_stmt_functs ->
    (Stmt.stmt_desc * ProgUtils.DisambiguationTbl.t) Rewriter.t

  (** Type-checks one entry of a [call_decl_contract_ext]/[loop_contract_ext] list
      against the declaring callable's/loop's formals (given via [call_decl] -- for a
      loop this is the [call_decl] of the tail-recursive procedure the loop is about to
      be rewritten into, since loop contracts are type-checked before that rewrite runs
      but share the same formal-scope shape). Takes and returns a whole [contract_ext]
      value. *)
  val type_check_contract_ext :
    Callable.call_decl ->
    Stmt.contract_ext ->
    location ->
    ProgUtils.DisambiguationTbl.t ->
    type_check_stmt_functs ->
    Stmt.contract_ext Rewriter.t

  (** Called once for every group of mutually-recursive callables (a strongly-connected
      component of the call graph with more than one member) found in a module, given
      every member's [call_decl]. [type_check_contract_ext] above only ever sees one
      callable at a time, so it can't check a property that has to hold *across* a
      group -- e.g. [DecreasesExt] uses this to require that if any member of the group
      has a `decreases` clause, every member does (an unguarded edge in the cycle would
      mean the cycle's termination isn't actually proved) and that all members' clauses
      share the same lexicographic shape, raising a located [Util.Error] otherwise.
      Singleton groups (including self-recursive ones) are never passed to this hook --
      a lone callable's own clause is already fully checked by
      [type_check_contract_ext]. Default (no active contract extension, or a group none
      of them care about) is to do nothing. *)
  val check_contract_ext_group_compatible : Callable.call_decl list -> unit Rewriter.t


  (* Rewrites *)
  val rewrite_type_ext : Ast.Type.type_ext -> type_expr list -> location -> type_expr Rewriter.t

  val rewrite_expr_ext : Expr.expr_ext -> expr list -> Expr.expr_attr -> expr Rewriter.t

  val rewrite_basic_stmt_ext : Stmt.stmt_ext -> expr list -> location -> Stmt.t Rewriter.t

  (** The [stmt_desc]-level sibling of [rewrite_basic_stmt_ext], for the self-contained
      [Stmt.StmtExt] extension point. *)
  val rewrite_stmt_ext : Stmt.stmt_ext -> location -> Stmt.t Rewriter.t

  (** Called once for every call site found in a [Proc]/[Lemma] body whose *callee*
      has a non-empty [call_decl_contract_ext] (or, for [Func]s, at the point
      [rewrite_add_func_contract_lemmas] emits a call to a companion auto-lemma, for
      every eligible-func call) where [caller_call_decl] and [callee_call_decl] denote
      the calling and called callable's declarations, the [bool] says whether caller and
      callee lie in the same strongly-connected component of the module's call graph
      (always [true] for a literal self-call; also [true] for any two callables that are
      mutually recursive with each other, even through intermediate calls -- computed
      once per module from the whole call graph, see [lib/frontend/rewrites/rewrites.ml]),
      and [call_args] are the actual arguments of that call. Returns statements
      (typically an assert) to insert immediately before the call. This is *not*
      restricted to recursive calls -- caller and callee may be entirely unrelated
      callables, and the [bool] is [false] for such a call; it's up to the extension to
      decide, from [caller_call_decl]/[callee_call_decl]/the [bool], whether and how
      they're related (e.g. [DecreasesExt] only acts when the [bool] is [true], i.e. for
      calls within a recursive group, self- or mutually-recursive alike -- but a
      different contract extension might care about every call to a given callable
      regardless of recursion). Core code invokes this uniformly for every candidate
      call site -- it does not know what [call_decl_contract_ext] means, only that some
      extension may want to instrument the call; the default (no active contract
      extension) is to return no extra statements. *)
  val rewrite_contract_ext_call :
    Callable.call_decl ->
    Callable.call_decl ->
    bool ->
    expr list ->
    location ->
    Stmt.t list Rewriter.t

  (** Called once for every [Proc]/[Lemma] callable, before any of its statements are
      visited by [rewrite_contract_ext_call] above (or by anything else). Returns
      statements to prepend at the very top of the callable's body. Not tied to
      [contract_ext] at all -- any extension can use this for whatever per-callable
      body setup it needs, e.g. introducing (via [Rewriter.introduce_symbol]) and
      initializing ghost locals sized/typed however that specific callable requires.
      [DecreasesExt] uses it to snapshot a `decreases` measure's entry-time value,
      needed because the measure may itself be reassigned by the body before a
      recursive call is reached (see lib/ext/README.md, "Rewrites"). This is also the
      general replacement for what a fixed-size, uniformly-added-to-every-callable
      pool of scratch locals would otherwise be used for: unlike such a pool, what
      gets introduced here can vary per callable (in count, in type, in name) and
      costs nothing for callables that don't need it. Default (no active extension
      using this hook) is to prepend nothing. *)
  val rewrite_callable_entry :
    Callable.call_decl -> Stmt.t list Rewriter.t

  (** Called by [rewrite_loops] for every entry of a loop's [loop_contract_ext] as it
      transfers that entry onto the synthesized tail-recursive procedure's
      [call_decl_contract_ext]. [subst] is the same substitution [rewrite_loops] applies
      to [loop_contract] (loop-local variables -> the synthesized procedure's fresh
      formals); an extension applies it to whatever expressions its value carries, and
      may also swap in loop-specific wording (e.g. via a payload that reuses
      [Stmt.spec]'s [spec_error], the same mechanism [rewrite_stmt_error_msg]'s [Loop]
      case already uses for invariants) -- capturing the original location before
      calling [subst], not after, since substituting a bare-identifier expression
      replaces the whole node. Pure and total: default (no active contract extension,
      or a tag the extension doesn't recognize) is the identity. *)
  val rewrite_contract_ext_loop_transfer :
    subst:(expr -> expr) -> Stmt.contract_ext -> Stmt.contract_ext

  val lib_sources : (string * string) list
end


module type ListFns = sig
    val listTpConstr : unit -> Type.type_ext
    val mk_list_tp : location -> type_expr -> type_expr 
    val ls_cons : location -> expr -> expr -> expr
    val ls_nil : location -> elem_typ:type_expr -> unit -> expr
    val ls_hd : location -> expr -> expr
    val ls_tl : location -> expr -> expr
    val ls_len : location -> expr -> expr
    val list_tp_to_elem_typ : type_expr -> type_expr option
  end

(* ListAPI for extensions that depend on lists such as ProphecyExt and ErrorCreditsExt *)
module type ListApi = sig
  include Ext

  module ListFns: ListFns
end
