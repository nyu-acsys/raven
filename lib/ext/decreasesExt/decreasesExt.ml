open Base
open Ast
open ExtApi
open Util

(** Implements termination checking via `decreases` contract clauses. This extension
    adds a contract-level clause -- rather than a new type/expr/stmt construct -- so it
    uses the [contract_ext] extension point instead of [type_ext]/[expr_ext]/[stmt_ext].

    `decreases e1, ..., en` on a `func`/`proc`/`lemma` (or a `while` loop) declares a
    termination measure: a lexicographic tuple of expressions over the callable's own
    parameters, each ranging over any type with a [Library.WellFoundedOrder] instance,
    resolved from the expression's own type via [is_wf_order_type] -- see
    well_founded_order.rav (this extension's own library, shipped via [lib_source]
    below rather than the generic standard library) for the shipped instances
    (`IntOrder`, `Ordinal`, `LexOrder`, `MultisetOrder`) and why fixed-arity
    lexicographic tuples of `Int` alone aren't enough to express e.g. a
    multiset-based termination argument.

    The clause's payload is a [Stmt.spec list], one [spec] per lexicographic component,
    reusing [spec]'s existing [spec_form]/[spec_error] machinery -- this is what lets a
    loop-transferred `decreases` clause report "this loop may not terminate" at the
    clause's own source location, the same way a failing loop invariant does, instead
    of naming the internal synthesized procedure (see [rewrite_contract_ext_loop_transfer]).

    For every call found within a strongly-connected component of the module's call
    graph -- self-recursive calls, and (Phase 2) calls between distinct
    mutually-recursive callables alike -- found in a `proc`/`lemma` body, and for every
    such call `rewrite_add_func_contract_lemmas` emits inside a `func`'s companion
    auto-lemma, this extension inserts an assertion that the *callee's* measure
    evaluated at the call's actual arguments is lexicographically smaller than the
    *caller's* measure evaluated at the caller's own entry-time parameter values.
    Checking is opt-in per callable in the sense that a recursive callable with no
    `decreases` clause is left exactly as it was before this extension existed --
    *unless* it's part of a mutually-recursive group (a strongly-connected component
    with more than one member) where some *other* member does declare one, in which
    case leaving it unchecked would give a false sense of a proved termination
    guarantee for the whole cycle, so [check_contract_ext_group_compatible] rejects
    that as a hard error instead (see its doc comment). Members of such a group must
    also all declare measures of the same lexicographic arity, using the same
    [WellFoundedOrder] instance at each position, checked by the same hook. *)

(* DecreasesExt itself doesn't use lists, but sits below ProphecyExt/ErrorCreditsExt in
   the stack (see lib/ext/ext.ml), both of which require a ListApi Cont. *)
module DecreasesExt (Cont : ListApi) = struct
  (* Every hook defaults to Cont's (including ListFns, since Cont : ListApi); only the
     ones actually overridden below need a definition. *)
  include Cont

  let lib_source = Some ("well_founded_order.rav", [%blob "well_founded_order.rav"])

  (** ExtApi/core has no notion of [WellFoundedOrder] -- this is entirely
      DecreasesExt's own vocabulary, resolved on demand here rather than
      cached in a core-AST field the way [mod_decl_is_ra] is (that field is
      legitimate on [Module.mod_decl] because resource algebras are a core
      language concept; well-founded orders are purely this extension's
      concern). [mod_decl_interfaces]/[mod_decl_rep] are already generic core
      fields used by core's own interface-conformance checking (not
      RA-specific), and [Rewriter.find]/[resolve_and_find] are already
      reachable via [Ast]'s wholesale re-export, so no ExtApi or core changes
      are needed -- only a private walk mirroring
      [ProgUtils.is_ra_type]/[does_ident_implement_ra] and [typing.ml]'s
      [mod_decl_is_ra] computation (used here only as a design template, not
      shared code). Not cached: every [WellFoundedOrder] instance shipped in
      the standard library implements it directly (interface depth 1), so a
      fresh walk per query is cheap enough that a shared cache isn't worth
      the trouble of threading through disjoint [ExtApi] hook invocations. *)
  let lib_wf_order_qual_ident =
    QualIdent.from_list [ Predefs.lib_ident; Ident.make Loc.dummy "WellFoundedOrder" 0 ]

  let lib_int_order_qual_ident =
    QualIdent.from_list [ Predefs.lib_ident; Ident.make Loc.dummy "IntOrder" 0 ]

  (* Checks whether [target] is (transitively) among [interfaces] -- some member
     either *is* [target], or itself (transitively) implements it. [visited]
     guards against cycles in the interface graph: [Type], the universal base
     interface every other interface (transitively) ascribes to, ascribes to
     itself -- so an unguarded walk of [mod_decl_interfaces] loops forever the
     first time it reaches [Type] (or any other self- or mutually-referential
     interface), no different from any other graph walk needing a visited set. *)
  let interfaces_include (target : qual_ident) (interfaces : QualIdentSet.t) : bool Rewriter.t =
    let open Rewriter.Syntax in
    let rec go (visited : QualIdentSet.t) (interfaces : QualIdentSet.t) : bool Rewriter.t =
      Rewriter.List.exists (Set.to_list interfaces) ~f:(fun iface_ident ->
          let* iface_qi, iface_symbol = Rewriter.resolve_and_find iface_ident in
          if QualIdent.equal iface_qi target then Rewriter.return true
          else if Set.mem visited iface_qi then Rewriter.return false
          else
            Rewriter.Symbol.extract iface_symbol ~f:(fun _ _ -> function
              | Module.ModDef m -> go (Set.add visited iface_qi) m.mod_decl.mod_decl_interfaces
              | _ -> Rewriter.return false))
    in
    go (Set.empty (module QualIdent)) interfaces

  (* Same cycle concern as [interfaces_include] applies to the [ModInst] chain
     below (a module instantiation's [mod_inst_type]/[mod_inst_def] could in
     principle reference back to a qual_ident already being resolved), so this
     also threads a [visited] set rather than assuming the chain is acyclic. *)
  let does_module_implement_wf_order (module_qident : qual_ident) (type_ident : ident) : bool Rewriter.t =
    let open Rewriter.Syntax in
    let rec go (visited : QualIdentSet.t) (module_qident : qual_ident) : bool Rewriter.t =
      if Set.mem visited module_qident then Rewriter.return false
      else
        let visited = Set.add visited module_qident in
        let* symbol = Rewriter.find module_qident in
        Rewriter.Symbol.extract symbol ~f:(fun _ _ -> function
          | Module.ModDef m -> (
            match m.mod_decl.mod_decl_rep with
            | Some id when Ident.equal id type_ident ->
              interfaces_include lib_wf_order_qual_ident m.mod_decl.mod_decl_interfaces
            | _ -> Rewriter.return false)
          | ModInst mod_inst -> (
            let* is_wf = go visited mod_inst.mod_inst_type in
            if is_wf then Rewriter.return true
            else
              match mod_inst.mod_inst_def with
              | None -> Rewriter.return false
              | Some (mod_inst_def_funct, _) -> go visited mod_inst_def_funct)
          | _ -> Rewriter.return false)
    in
    go (Set.empty (module QualIdent)) module_qident

  (* Resolves [tp] to its own qual_ident and [variant_decl list] if [tp] is a
     `data` type, [None] otherwise -- the same walk [AtomicExt.is_type_word_sized]
     already does for a different purpose (there: are all constructors
     base-typed; here: what are the self-recursive field positions). *)
  let as_data_type (tp : type_expr) : (qual_ident * Type.variant_decl list) option Rewriter.t =
    let open Rewriter.Syntax in
    match tp with
    | App (Var qi, [], _) ->
      let* qi, symbol = Rewriter.resolve_and_find qi in
      let+ type_def = Rewriter.Symbol.reify_type_def (QualIdent.to_loc qi) symbol in
      (match type_def with
       | Some (App (Data (data_qi, variant_decls), [], _)) -> Some (data_qi, variant_decls)
       | _ -> None)
    | _ -> Rewriter.return None

  (* A field of some variant of [data_qi] counts as a recursive position exactly
     when its own type refers back to [data_qi] itself. Fields of any other type
     -- a type parameter (e.g. [List[E]]'s [E]), or a *different* data type,
     including one that's part of a cycle back to this one (mutual recursion) --
     are simply never recursed into by [mk_auto_order_lt_body] below: sound
     either way (never over-claims a decrease), just incomplete for anything
     beyond straightforward self-recursion, which is this scheme's deliberately
     chosen scope for now. *)
  let is_self_recursive_field (data_qi : qual_ident) (field : var_decl) : bool =
    match field.var_type with
    | App (Var qi, [], _) -> QualIdent.equal qi data_qi
    | _ -> false

  (* Builds `lt`'s body for the auto-generated order below. Raven has no match
     expression, so -- exactly like every hand-written `data`-type function in
     this codebase, e.g. [OrdinalBase.lt] -- [y]'s own constructor is
     exhaustively discriminated via reconstruct-and-compare, `y == C(y.f1, ...,
     y.fn)`; for the matching variant, `x` "decreases" `y` iff `x` equals one of
     that variant's self-recursive fields. Deliberately *not* transitively
     closed (i.e. this only ever looks one field-selection deep, never `x ==
     y.f.g` or "recursing into" the disjunction): a `decreases` progress check
     only ever needs a single-step comparison -- the actual call argument
     against the caller's own entry-time value -- and a self-referential
     definition of `lt` itself would risk an E-matching trigger loop for no
     actual gain, since the sequence of single-step decreases across a whole
     recursive call chain is what gives termination, not transitivity baked
     into `lt`. *)
  let mk_auto_order_lt_body ~(loc : location) (data_qi : qual_ident)
      (variant_decls : Type.variant_decl list) (x_vd : var_decl) (y_vd : var_decl) : expr =
    let module_qi = QualIdent.pop data_qi in
    let x_expr = Expr.from_var_decl x_vd in
    let y_expr = Expr.from_var_decl y_vd in
    let field_expr (fvd : var_decl) =
      let destr_qi = QualIdent.append module_qi fvd.var_name in
      Expr.mk_app ~loc ~typ:fvd.var_type (DataDestr destr_qi) [ y_expr ]
    in
    let rec go = function
      | [] -> Expr.mk_bool ~loc false
      | (variant : Type.variant_decl) :: rest ->
        let is_this_variant =
          let constr_qi = QualIdent.append module_qi variant.variant_name in
          let reconstructed =
            Expr.mk_app ~loc ~typ:y_vd.var_type (DataConstr constr_qi)
              (List.map variant.variant_args ~f:field_expr)
          in
          Expr.mk_eq ~loc y_expr reconstructed
        in
        let this_branch =
          match List.filter variant.variant_args ~f:(is_self_recursive_field data_qi) with
          | [] -> Expr.mk_bool ~loc false
          | recursive_fields ->
            Expr.mk_or ~loc (List.map recursive_fields ~f:(fun fvd -> Expr.mk_eq ~loc x_expr (field_expr fvd)))
        in
        Expr.mk_ite ~loc is_this_variant this_branch (go rest)
    in
    go variant_decls

  (* [is_wf_order_type] runs from both the type-checking pass and (again, per
     [type_check_contract_ext]'s own doc comment on why a clause is re-type-checked
     a second time) the rewrite pass, each with a different "current scope" --
     [introduce_typecheck_symbol'] resolves a symbol's target scope relative to
     that, so the same deterministic name from two different scopes lands two
     distinct qual_idents, not one reused one; a fresh name every call keeps that
     safe instead of relying on cross-call reuse. Harmless: [lt] carries no
     [ensures], hence no proof obligation, so a handful of redundant copies cost
     only elaboration bookkeeping, never SMT effort. *)
  let auto_order_module_ident (data_qi : qual_ident) : ident =
    Ident.fresh (QualIdent.to_loc data_qi) ("$decreases_auto_order$" ^ QualIdent.to_string data_qi)

  (* Synthesizes a module containing just a `lt` function for the `data` type
     [data_qi]/[variant_decls], trusting
     -- not proving -- that it's well-founded: unlike a real [WellFoundedOrder]
     instance, this has no [embed]/[lt_embed_mono] at all, since nothing
     [decreasesExt.ml] generates ever needs them for anything but the
     interface-conformance bookkeeping this deliberately opts out of (see
     [WellFoundedOrder]'s own doc comment). The trust this leans on -- that
     structural descent on an inductively-defined `data` type terminates -- is
     not a new assumption specific to this scheme: it's the same meta-theoretic
     fact [OrdinalBase.lt]'s own well-foundedness already rests on (see its doc
     comment), just applied directly instead of via an embedding proof. *)
  let auto_order_module_qual_ident ~(loc : location) (data_qi : qual_ident)
      (variant_decls : Type.variant_decl list) (measure_type : type_expr) : qual_ident Rewriter.t =
    let x_vd = Type.mk_var_decl ~const:true (Ident.make loc "x" 0) measure_type in
    let y_vd = Type.mk_var_decl ~const:true (Ident.make loc "y" 0) measure_type in
    let res_vd = Type.mk_var_decl ~const:true (Ident.make loc "res" 0) Type.bool in
    let lt_call_decl : Callable.call_decl = {
      call_decl_kind = Func;
      call_decl_name = Ident.make loc "lt" 0;
      call_decl_formals = [ x_vd; y_vd ];
      call_decl_returns = [ res_vd ];
      call_decl_locals = [];
      call_decl_precond = [];
      call_decl_postcond = [];
      call_decl_contract_ext = [];
      call_decl_status = NotFree;
      call_decl_is_auto = false;
      call_decl_needs_mask = None;
      call_decl_grants_mask = None;
      call_decl_loc = loc;
    } in
    let lt_call_def =
      Callable.FuncDef { func_body = Some (mk_auto_order_lt_body ~loc data_qi variant_decls x_vd y_vd) }
    in
    let module_symbol =
      Module.ModDef {
        mod_decl = { Module.empty_decl with mod_decl_name = auto_order_module_ident data_qi; mod_decl_loc = loc };
        mod_def = [ SymbolDef (CallDef { call_decl = lt_call_decl; call_def = lt_call_def }) ];
      }
    in
    Rewriter.introduce_typecheck_symbol' ~loc module_symbol

  (* Resolves the [WellFoundedOrder] instance (as the qual_ident of the module
     implementing it) for a `decreases` measure component's type, if any. [Int]
     is special-cased to the library's [IntOrder]: it's a primitive type, not a
     module-owned rep type the [App (Var qi, [], _)] pattern below can walk to.
     A `data` type with no explicit [WellFoundedOrder]-implementing wrapper falls
     through to [auto_order_module_qual_ident] instead of [None] -- see its own
     doc comment for what that trades away. *)
  let is_wf_order_type (tp : type_expr) : qual_ident option Rewriter.t =
    let open Rewriter.Syntax in
    match tp with
    | App (Int, [], _) -> Rewriter.return (Some lib_int_order_qual_ident)
    | App (Var qi, [], _) as tp ->
      let module_qi = QualIdent.pop qi in
      let* is_wf = does_module_implement_wf_order module_qi (QualIdent.unqualify qi) in
      if is_wf then Rewriter.return (Some module_qi)
      else
        let* data_type = as_data_type tp in
        (match data_type with
         | None -> Rewriter.return None
         | Some (data_qi, variant_decls) ->
           let+ order_qi = auto_order_module_qual_ident ~loc:(Type.to_loc tp) data_qi variant_decls tp in
           Some order_qi)
    | _ -> Rewriter.return None

  let get_wf_order_lt_fn_qual_ident (instance_qi : qual_ident) : qual_ident =
    QualIdent.append instance_qi (Ident.make (QualIdent.to_loc instance_qi) "lt" 0)

  (* [is_wf_order_type], unwrapped: safe to call anywhere a measure component's
     type has already passed [type_check_contract_ext] (which rejects types with
     no [WellFoundedOrder] instance), so [None] here would indicate a compiler
     bug, not a user error. *)
  let wf_order_instance_of ~loc (tp : type_expr) : qual_ident Rewriter.t =
    let open Rewriter.Syntax in
    let+ wf_order = is_wf_order_type tp in
    match wf_order with
    | Some qi -> qi
    | None ->
      Error.internal_error loc
        "decreases: measure component has no WellFoundedOrder instance (should have been rejected \
         at type-checking time)"

  (* Deterministic (not fresh) so that the initializing assignment
     [rewrite_callable_entry] prepends and the read-back [rewrite_contract_ext_call]
     does at a later call site name the same ghost local, with no state shared
     between those two call sites beyond [call_decl] itself. One variable per
     callable, not one per lexicographic component: its type is a tuple sized to
     exactly that callable's own `decreases` clause (via
     [Type.mk_prod]/[decreases_snapshot_type] below), so there's no static cap on how
     many measure components a clause can have -- unlike a fixed-size pool of
     scratch locals declared once, uniformly, for every callable (which is exactly
     what [rewrite_callable_entry] replaces the need for; see [Config] in
     lib/ext/README.md), a tuple type's arity is whatever a specific clause needs.
     [Type.mk_prod] (and [Expr.mk_tuple]/[Expr.mk_tuple_lookup] below) already
     collapse the 1-component case to a bare component type, no tuple wrapper,
     so `decreases n` doesn't pay for tuple-ness it doesn't need. *)
  let decreases_snapshot_ident (call_decl : Callable.call_decl) : Ident.t =
    Ident.make call_decl.call_decl_loc ("$decreases_" ^ Ident.to_string call_decl.call_decl_name) 0

  (* Built from each component's own type: a measure component can be any type
     with a [WellFoundedOrder] instance, so the snapshot tuple's field types
     have to match, or the ghost local ends up mistyped relative to what's
     actually assigned into it. *)
  let decreases_snapshot_type (call_decl : Callable.call_decl) (component_types : type_expr list) : type_expr =
    Type.mk_prod call_decl.call_decl_loc component_types

  (** Tag for `decreases` clauses. Carries one [Stmt.spec] per lexicographic measure
      component directly (unlike [BasicStmtExt]/[TypeExt]/[ExprExt], [contract_ext] values
      own their whole payload rather than sharing a generic [expr list] alongside the
      tag), so each component gets its own location and (after
      [rewrite_contract_ext_loop_transfer]) its own error message for free. *)
  type Stmt.contract_ext += Decreases of Stmt.spec list

  let default_measure_error (spec_form : expr) : (qual_ident -> location -> Error.t) =
    Stmt.mk_const_spec_error
      ( Error.Verification, Expr.to_loc spec_form,
        "This decreases clause's termination measure may not decrease on this \
         recursive call" )

  (** Finds the `decreases` clause (if any) declared on [call_decl], as the raw list of
      per-component specs (in terms of [call_decl]'s own formals). *)
  let find_decreases_measure (call_decl : Callable.call_decl) : Stmt.spec list option =
    List.find_map call_decl.call_decl_contract_ext ~f:(function
      | Decreases specs -> Some specs
      | _ -> None)

  (** AstDef *)
  (* type_ext_to_name/expr_ext_to_string/pr_basic_stmt_ext/basic_stmt_ext_*/
     pr_stmt_ext/stmt_ext_*/type_ext_is_recognized/expr_ext_is_recognized/
     stmt_ext_is_recognized: no type_ext/expr_ext/stmt_ext constructors here (this
     extension only adds a contract_ext), so Cont's default is used for all of them. *)

  let contract_ext_to_string (contract_ext : Stmt.contract_ext) : string =
    match contract_ext with
    | Decreases specs ->
      "decreases " ^ String.concat ~sep:", " (List.map specs ~f:(fun s -> Expr.to_string s.Stmt.spec_form))
    | _ -> Cont.contract_ext_to_string contract_ext

  let contract_ext_is_recognized contract_ext =
    match contract_ext with
    | Decreases _ -> true
    | _ -> Cont.contract_ext_is_recognized contract_ext

  (* Rewriter *)
  (* expr_ext_rewrite_types/basic_stmt_ext_rewrite_types/stmt_ext_rewrite: no
     type_ext/stmt_ext constructors here, so Cont's default is used. *)

  let contract_ext_rewrite_exprs ~(f : expr -> expr Rewriter.t) (contract_ext : Stmt.contract_ext) :
      Stmt.contract_ext Rewriter.t =
    let open Rewriter.Syntax in
    match contract_ext with
    | Decreases specs ->
      let+ specs =
        Rewriter.List.map specs ~f:(fun spec ->
            let+ spec_form = f spec.Stmt.spec_form in
            { spec with Stmt.spec_form })
      in
      Decreases specs
    | _ -> Cont.contract_ext_rewrite_exprs ~f contract_ext

  (* Typing *)
  (* type_check_type_expr/type_check_expr/type_check_basic_stmt/type_check_stmt_ext:
     no type_ext/expr_ext/stmt_ext constructors here, so Cont's default is used. *)

  (** Type-checks the measure expressions of a single `decreases` clause against the
      declaring callable's/loop's formals, and installs the generic fallback error
      message (mirroring how [rewrite_stmt_error_msg] decorates ordinary asserts) --
      this has to happen here, not later, because the recursive-call asserts this
      extension inserts are built by passes that run *after* [rewrite_stmt_error_msg],
      so they'd otherwise get no error message at all (an empty [spec_error] makes the
      checker fail with no reported error, see WISHLIST.md). [rewrite_contract_ext_loop_transfer]
      overrides this default for loop-derived clauses. Each component's type is
      inferred and must resolve to a [WellFoundedOrder] instance via
      [is_wf_order_type]; a lexicographic tuple is just a list of such
      components, each independently resolved. *)
  let type_check_contract_ext (call_decl : Callable.call_decl)
      (contract_ext : Stmt.contract_ext) (loc : location)
      (disam_tbl : ProgUtils.DisambiguationTbl.t)
      (type_check_stmt_functs : type_check_stmt_functs) :
      Stmt.contract_ext Rewriter.t =
    let open Rewriter.Syntax in
    match contract_ext with
    | Decreases specs ->
      if List.is_empty specs then
        Error.type_error loc "decreases clause expects at least one measure expression"
      else
        (* [call_decl]'s own body/contract is a ghost scope precisely when
           [Callable.is_ghost_kind] says so (e.g. a [Lemma]); a measure expression
           referencing a value that's only meaningful there (e.g. a lemma-local
           variable) needs the same ghost expectation, or [disambiguate_process_expr]
           rejects it as "reads ghost state" -- mirroring how ordinary expression
           processing derives its own expected ghost-ness (see [Typing.ml]'s repeated
           [Type.set_ghost var_ghost]/[Type.set_ghost is_ghost_scope] pattern). *)
        let expected_typ = Type.any |> Type.set_ghost (Callable.is_ghost_kind call_decl.call_decl_kind) in
        let+ specs =
          Rewriter.List.map specs ~f:(fun spec ->
              let* spec_form =
                type_check_stmt_functs.disambiguate_process_expr spec.Stmt.spec_form expected_typ disam_tbl
              in
              let* wf_order = is_wf_order_type (Expr.to_type spec_form) in
              match wf_order with
              | None ->
                Error.type_error (Expr.to_loc spec_form)
                  "this decreases clause's measure type has no WellFoundedOrder instance"
              | Some _ ->
                (* Only install the generic default the first time this clause is
                   type-checked (right after parsing, when [spec_error] is still the
                   parser's [[]]). A loop-derived clause gets re-type-checked when
                   [rewrite_loops] introduces its synthesized procedure
                   ([Rewriter.introduce_typecheck_symbol']), by which point
                   [rewrite_contract_ext_loop_transfer] has already set a loop-specific
                   [spec_error] -- overwriting it unconditionally here would silently
                   discard that wording. *)
                let spec_error =
                  if List.is_empty spec.Stmt.spec_error then [ default_measure_error spec_form ]
                  else spec.spec_error
                in
                Rewriter.return { spec with Stmt.spec_form; spec_error })
        in
        Decreases specs
    | _ -> Cont.type_check_contract_ext call_decl contract_ext loc disam_tbl type_check_stmt_functs

  (** Called once for every recursive call-graph component -- a self-loop singleton, or
      a strongly-connected component with more than one member (mutual recursion).
      Library-rooted members are already filtered out by the caller. If none declare a
      `decreases` clause, there's nothing to check here for correctness (the group
      stays entirely unchecked, exactly as any recursive callable without a clause
      always has) -- though under `--strict`, every recursive `Lemma`/`Func` among them
      gets a warning (see below). If *some* do and others don't, that's a hard error: an
      unguarded edge in the cycle means the cycle's termination isn't actually proved,
      even though it might look checked at a glance -- see the file-level doc comment.
      If *all* do, they must share the same lexicographic arity, since
      [rewrite_contract_ext_call] below zips a caller's measure against a callee's
      one-for-one, and the same [WellFoundedOrder] instance (see
      [type_check_contract_ext]) at each position: [mk_progress_check] compares a
      caller's entry-time measure against a callee's call-time measure componentwise
      using whichever instance the *caller's* component type resolves to, so a
      callee using a different instance at that position would silently compare
      values from two unrelated orders. (The arity/instance checks below still just
      no-op for a singleton, since [with_measure]/[without_measure] can't disagree with
      themselves -- no special-casing needed for the now-possible 1-element case.) *)
  let check_contract_ext_group_compatible (call_decls : Callable.call_decl list) : unit Rewriter.t =
    let open Rewriter.Syntax in
    let with_measure, without_measure =
      List.partition_map call_decls ~f:(fun call_decl ->
          match find_decreases_measure call_decl with
          | Some specs -> First (call_decl, specs)
          | None -> Second call_decl)
    in
    let* () =
      match with_measure, without_measure with
      | [], _ | _, [] -> Rewriter.return ()
      | _, missing :: _ ->
        let covered = List.map with_measure ~f:(fun (cd, _) -> Ident.to_string cd.call_decl_name) in
        Error.type_error missing.call_decl_loc
          (Printf.sprintf
             "%s does not declare a `decreases` clause, but it is mutually recursive with %s, which \
              declare(s) one; every member of a mutually-recursive group must declare a `decreases` clause, \
              or none of them may -- otherwise this cycle's termination isn't actually guaranteed by the check"
             (Ident.to_string missing.call_decl_name)
             (String.concat ~sep:", " covered))
    in
    (* `--strict`: flag every recursive `Lemma`/`Func` left with no `decreases` clause
       at all -- not unsound to leave unchecked (partial correctness just gets no
       termination guarantee for it), but worth a warning. By this point the group's
       coverage is already known consistent (the mixed-coverage error above would have
       aborted first otherwise), so [without_measure] is never a half-covered group.
       [Proc] is excluded: partial correctness doesn't require procs to terminate.
       [Pred]/[Invariant] can't reach here with a body to be recursive in ([call_def] is
       [FuncDef], not [ProcDef]) other than through their own (non-loop) call graph, and
       aren't part of what soundness needs checked either. *)
    let* () =
      let* cli_config = Rewriter.current_cli_config in
      if not cli_config.cli_strict then Rewriter.return ()
      else begin
        List.iter without_measure ~f:(fun call_decl ->
            match call_decl.Callable.call_decl_kind with
            | Lemma | Func ->
              Logs.warn (fun m -> m "%s%s"
                (Loc.to_string call_decl.call_decl_loc)
                (Printf.sprintf
                   "%s is recursive but declares no `decreases` clause; its termination will be \
                    assumed for verification purposes, not checked"
                   (Ident.to_string call_decl.call_decl_name)))
            | Proc | Pred | Invariant -> ());
        Rewriter.return ()
      end
    in
    let* () =
      match with_measure with
      | [] | [ _ ] -> Rewriter.return ()
      | (first_decl, first_specs) :: rest ->
        let expected_arity = List.length first_specs in
        let* () =
          Rewriter.List.iter rest ~f:(fun (call_decl, specs) ->
              let arity = List.length specs in
              if arity <> expected_arity then
                Error.type_error call_decl.call_decl_loc
                  (Printf.sprintf
                     "this `decreases` clause has %d measure component(s), but %s (in the same \
                      mutually-recursive group) has %d; every member of a mutually-recursive group must \
                      declare `decreases` clauses of the same arity"
                     arity (Ident.to_string first_decl.call_decl_name) expected_arity)
              else Rewriter.return ())
        in
        let spec_instance (s : Stmt.spec) =
          wf_order_instance_of ~loc:(Expr.to_loc s.Stmt.spec_form) (Expr.to_type s.Stmt.spec_form)
        in
        let* first_instances = Rewriter.List.map first_specs ~f:spec_instance in
        Rewriter.List.iter rest ~f:(fun (call_decl, specs) ->
            let* instances = Rewriter.List.map specs ~f:spec_instance in
            match
              List.find (List.zip_exn first_instances instances) ~f:(fun (a, b) ->
                  not (QualIdent.equal a b))
            with
            | None -> Rewriter.return ()
            | Some _ ->
              Error.type_error call_decl.call_decl_loc
                (Printf.sprintf
                   "this `decreases` clause uses a different WellFoundedOrder instance than %s (in the \
                    same mutually-recursive group) at some lexicographic position; every member of a \
                    mutually-recursive group must use matching instances position-by-position"
                   (Ident.to_string first_decl.call_decl_name)))
    in
    Cont.check_contract_ext_group_compatible call_decls

  (* Rewrites *)
  (* rewrite_type_ext/rewrite_expr_ext/rewrite_basic_stmt_ext/rewrite_stmt_ext: no
     type_ext/expr_ext/stmt_ext constructors here, so Cont's default is used. *)

  let rewrite_contract_ext_loop_transfer ~(subst : expr -> expr) (contract_ext : Stmt.contract_ext) :
      Stmt.contract_ext =
    match contract_ext with
    | Decreases specs ->
      Decreases
        (List.map specs ~f:(fun spec ->
             (* Capture the original location before [subst], not after -- substituting
                a bare-identifier expression (the common case, e.g. `decreases i`)
                replaces the whole node, which would otherwise lose it. Mirrors how
                [rewrite_stmt_error_msg]'s [Loop] case captures [spec.spec_form]'s
                location in a closure before [rewrite_loops] alpha-renames it. *)
             let error =
               Stmt.mk_const_spec_error
                 ( Error.Verification, Expr.to_loc spec.Stmt.spec_form,
                   "This loop may not terminate: its decreases clause's termination \
                    measure may not decrease on every iteration" )
             in
             { spec with Stmt.spec_form = subst spec.spec_form; spec_error = [ error ] }))
    | _ -> Cont.rewrite_contract_ext_loop_transfer ~subst contract_ext

  (** Builds `measures_at_call` lexicographically-less-than `measures_at_entry`, i.e.
      the progress obligation for one recursive call. Both lists have the same length
      (checked during type-checking: both come from the same `decreases` clause, one
      evaluated at the callable's own formals, the other with those formals substituted
      by the call's actual arguments). Each component's "less than" is the [lt] of
      whichever [WellFoundedOrder] instance its type resolved to at type-checking time
      (re-resolved here via [is_wf_order_type] -- cheap and not worth threading through
      the [Decreases] payload, see that function's doc comment); [Int]'s "less than"
      already folds in "and non-negative" via the library's [IntOrder.lt]. *)
  let mk_progress_check ~loc (measures_at_entry : expr list) (measures_at_call : expr list) : expr Rewriter.t =
    let open Rewriter.Syntax in
    let rec go = function
      | [], [] -> Rewriter.return (Expr.mk_bool ~loc false)
      | e :: entry', c :: call' ->
        let* instance_qi = wf_order_instance_of ~loc:(Expr.to_loc e) (Expr.to_type e) in
        let this_component_decreases =
          Expr.mk_app ~loc ~typ:Type.bool (Expr.Var (get_wf_order_lt_fn_qual_ident instance_qi)) [ c; e ]
        in
        let this_component_equal = Expr.mk_eq ~loc c e in
        let+ rest = go (entry', call') in
        Expr.mk_or ~loc [ this_component_decreases; Expr.mk_and ~loc [ this_component_equal; rest ] ]
      | _, _ ->
        Error.internal_error loc "decreases: mismatched measure arity between call site and declaration"
    in
    go (measures_at_entry, measures_at_call)

  (* Projects the [i]-th lexicographic component back out of the (possibly
     tuple-typed, possibly -- for a single-component clause -- bare) snapshot
     variable for [call_decl]. [Expr.mk_tuple_lookup] handles both shapes. *)
  let decreases_snapshot_exprs (call_decl : Callable.call_decl) (measures : expr list) : expr list =
    let snap_expr =
      Expr.mk_var ~typ:(decreases_snapshot_type call_decl (List.map measures ~f:Expr.to_type))
        (QualIdent.from_ident (decreases_snapshot_ident call_decl))
    in
    List.mapi measures ~f:(fun i _ -> Expr.mk_tuple_lookup snap_expr i)

  (** [Proc]/[Lemma] formals can be reassigned by the body before a recursive call is
      reached (this is exactly how the tail-recursive procedure [rewrite_loops]
      generates for a `while` loop works), so "the measure at entry" cannot just mean
      "the clause's expressions evaluated at the formals" -- read at the call site,
      those would already reflect any prior mutation, same as "the measure at the
      call", making the progress check vacuous. This snapshots the entry-time value
      into a ghost local -- introduced here, since its type depends on this specific
      callable's own `decreases` clause, which a fixed, uniformly-declared pool
      couldn't give it -- for exactly this reason; this is the per-callable prepend
      pass, run once before any call site is visited. This is a general (not
      contract_ext-specific) hook, so it runs unconditionally for every `Proc`/
      `Lemma` in the program; the [find_decreases_measure] check below is what keeps
      this a no-op for the overwhelming majority of callables, which have no
      `decreases` clause at all. *)
  let rewrite_callable_entry (call_decl : Callable.call_decl) :
      Stmt.t list Rewriter.t =
    let open Rewriter.Syntax in
    let* own_stmts =
      match call_decl.call_decl_kind with
      | Func | Pred | Invariant -> Rewriter.return []
      | Proc | Lemma ->
        (match find_decreases_measure call_decl with
         | None -> Rewriter.return []
         | Some specs ->
           let loc = call_decl.call_decl_loc in
           let snap_ident = decreases_snapshot_ident call_decl in
           let snap_type =
             decreases_snapshot_type call_decl (List.map specs ~f:(fun s -> Expr.to_type s.Stmt.spec_form))
           in
           let snap_var_decl = Type.mk_var_decl ~ghost:true ~loc snap_ident snap_type in
           let+ () =
             Rewriter.introduce_symbol
               (Module.VarDef { var_decl = snap_var_decl; var_init = None; var_is_free = false })
           in
           let tuple_expr = Expr.mk_tuple ~loc (List.map specs ~f:(fun s -> s.Stmt.spec_form)) in
           [ Stmt.mk_assign ~loc ~is_init:true [ QualIdent.from_ident snap_ident ] tuple_expr ])
    in
    let+ cont_stmts = Cont.rewrite_callable_entry call_decl in
    own_stmts @ cont_stmts

  let rewrite_contract_ext_call (caller_call_decl : Callable.call_decl)
      (callee_call_decl : Callable.call_decl) (in_same_scc : bool) (call_args : expr list) (loc : location) :
      Stmt.t list Rewriter.t =
    let open Rewriter.Syntax in
    let* own_checks =
      if not in_same_scc then
        (* An ordinary non-recursive call to a decreases-bearing callable is correctly
           a no-op here -- nothing to check unless caller and callee are (mutually or
           self-) recursive with each other. *)
        Rewriter.return []
      else
        match find_decreases_measure caller_call_decl, find_decreases_measure callee_call_decl with
        | None, _ | _, None ->
          (* Unreachable for a genuine (>1-member) mutually-recursive group:
             [check_contract_ext_group_compatible] already rejects a group where some
             members have a `decreases` clause and others don't, before this code ever
             runs. For the singleton self-loop case (caller == callee), this is
             exactly Phase 1's "no clause, nothing to check" no-op. *)
          Rewriter.return []
        | Some caller_specs, Some callee_specs ->
          (* [spec_error] comes from the caller's own clause -- it's the caller's
             declared termination argument being checked at this call site, so its
             own wording (generic, or loop-specific via
             [rewrite_contract_ext_loop_transfer]) is what should be reported,
             mirroring how failing loop invariants point at the loop's own clause
             rather than the internal callable being checked. *)
          let spec_error = (List.hd_exn caller_specs).Stmt.spec_error in
          (* measures_at_call: the *callee's* own clause, evaluated at the call's
             actual arguments by substituting the callee's own formals -- not the
             caller's, which only coincided in Phase 1 because caller and callee were
             always the same callable there. *)
          let callee_subst_map =
            List.zip_exn
              (List.map callee_call_decl.call_decl_formals ~f:(fun vd -> QualIdent.from_ident vd.Type.var_name))
              call_args
            |> Map.of_alist_exn (module QualIdent)
          in
          let measures_at_call =
            List.map callee_specs ~f:(fun s -> Expr.alpha_renaming s.Stmt.spec_form callee_subst_map)
          in
          (* measures_at_entry: still the *caller's* own clause, exactly as in Phase 1. *)
          let caller_raw_measures = List.map caller_specs ~f:(fun s -> s.Stmt.spec_form) in
          let measures_at_entry =
            match caller_call_decl.call_decl_kind with
            | Proc | Lemma ->
              (* Read back the ghost snapshot [rewrite_callable_entry] initialized,
                 since the formals themselves may have been reassigned. *)
              decreases_snapshot_exprs caller_call_decl caller_raw_measures
            | Func | Pred | Invariant ->
              (* Func bodies are pure expressions -- the formals can't be reassigned,
                 so "entry" and "current" always coincide; no snapshot exists (or is
                 needed) for the func case, which piggybacks on the auto-lemma body. *)
              caller_raw_measures
          in
          (* [mk_progress_check] requires equal-length lists; guaranteed here by
             [check_contract_ext_group_compatible] for any real (>1-member) group,
             and trivially true for the singleton case where caller == callee (so
             caller_specs and callee_specs are the very same list). *)
          let+ check_expr = mk_progress_check ~loc measures_at_entry measures_at_call in
          [ Stmt.mk_assert_expr ~loc
              ~cmnt:"[EXT] DecreasesExt: termination measure must decrease on recursive call"
              ~spec_error
              check_expr
          ]
    in
    let* cont_checks = Cont.rewrite_contract_ext_call caller_call_decl callee_call_decl in_same_scc call_args loc in
    Rewriter.return (own_checks @ cont_checks)

  (* --------------------- *)
  (* --- DO NOT MODIFY --- *)
  let lib_sources = (Option.to_list lib_source) @ Cont.lib_sources
end
