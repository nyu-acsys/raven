open Base
open Ast
open ExtApi
open Util

(** Implements termination checking via `decreases` contract clauses. This extension
    adds a contract-level clause -- rather than a new type/expr/stmt construct -- so it
    uses the [contract_ext] extension point instead of [type_ext]/[expr_ext]/[stmt_ext].

    `decreases e1, ..., en` on a `func`/`proc`/`lemma` (or a `while` loop) declares a
    termination measure: a lexicographic tuple of expressions over the callable's own
    parameters, each ranging over a fixed well-founded domain. In v1 only `Int` (bounded
    below by 0) is supported; `Set`/`Multiset` are deferred (see README note below).

    The clause's payload is a [Stmt.spec list], one [spec] per lexicographic component,
    reusing [spec]'s existing [spec_form]/[spec_error] machinery -- this is what lets a
    loop-transferred `decreases` clause report "this loop may not terminate" at the
    clause's own source location, the same way a failing loop invariant does, instead
    of naming the internal synthesized procedure (see [rewrite_contract_ext_loop_transfer]).

    For every self-recursive call found in a `proc`/`lemma` body, and for every
    self-recursive call `rewrite_add_func_contract_lemmas` emits inside a `func`'s
    companion auto-lemma, this extension inserts an assertion that the measure
    evaluated at the call's actual arguments is lexicographically smaller than the
    measure evaluated at the enclosing callable's current parameter values. Checking is
    entirely opt-in: a recursive callable with no `decreases` clause is left exactly as
    it was before this extension existed.

    Mutually-recursive callables (Phase 2 of the WISHLIST plan) are out of scope here:
    this extension only recognizes calls back to the *same* callable. *)

module DecreasesExt (Cont : ListApi) = struct
  let lib_source = None

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
     collapse the 1-component case to a bare `Int`, no tuple wrapper, so
     `decreases n` doesn't pay for tuple-ness it doesn't need. *)
  let decreases_snapshot_ident (call_decl : Callable.call_decl) : Ident.t =
    Ident.make call_decl.call_decl_loc ("$decreases_" ^ Ident.to_string call_decl.call_decl_name) 0

  let decreases_snapshot_type (call_decl : Callable.call_decl) (arity : int) : type_expr =
    Type.mk_prod call_decl.call_decl_loc (List.init arity ~f:(fun _ -> Type.int))

  (* DecreasesExt itself doesn't use lists, but sits below ProphecyExt/ErrorCreditsExt
     in the stack (see lib/ext/ext.ml), both of which require a ListApi Cont. *)
  module ListFns = Cont.ListFns

  (** Tag for `decreases` clauses. Carries one [Stmt.spec] per lexicographic measure
      component directly (unlike [StmtExt]/[TypeExt]/[ExprExt], [contract_ext] values
      own their whole payload rather than sharing a generic [expr list] alongside the
      tag), so each component gets its own location and (after
      [rewrite_contract_ext_loop_transfer]) its own error message for free. *)
  type Stmt.contract_ext += Decreases of Stmt.spec list

  let default_measure_error (spec_form : expr) : (qual_ident -> location -> Error.t) =
    Stmt.mk_const_spec_error
      ( Error.Verification, Expr.to_loc spec_form,
        "This decreases clause's termination measure may not decrease on this \
         recursive call" )

  (** AstDef *)
  let type_ext_to_name = Cont.type_ext_to_name
  let expr_ext_to_string = Cont.expr_ext_to_string
  let pr_stmt_ext = Cont.pr_stmt_ext

  let contract_ext_to_string (contract_ext : Stmt.contract_ext) : string =
    match contract_ext with
    | Decreases specs ->
      "decreases " ^ String.concat ~sep:", " (List.map specs ~f:(fun s -> Expr.to_string s.Stmt.spec_form))
    | _ -> Cont.contract_ext_to_string contract_ext

  let stmt_ext_symbols = Cont.stmt_ext_symbols
  let stmt_ext_local_vars_modified = Cont.stmt_ext_local_vars_modified
  let stmt_ext_fields_accessed = Cont.stmt_ext_fields_accessed

  let type_ext_is_recognized = Cont.type_ext_is_recognized
  let expr_ext_is_recognized = Cont.expr_ext_is_recognized
  let stmt_ext_is_recognized = Cont.stmt_ext_is_recognized

  let contract_ext_is_recognized contract_ext =
    match contract_ext with
    | Decreases _ -> true
    | _ -> Cont.contract_ext_is_recognized contract_ext

  (* Rewriter *)
  let expr_ext_rewrite_types = Cont.expr_ext_rewrite_types
  let stmt_ext_rewrite_types = Cont.stmt_ext_rewrite_types

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
  let type_check_type_expr = Cont.type_check_type_expr
  let type_check_expr = Cont.type_check_expr
  let type_check_stmt = Cont.type_check_stmt

  (** Type-checks the measure expressions of a single `decreases` clause against the
      declaring callable's/loop's formals, and installs the generic fallback error
      message (mirroring how [rewrite_stmt_error_msg] decorates ordinary asserts) --
      this has to happen here, not later, because the recursive-call asserts this
      extension inserts are built by passes that run *after* [rewrite_stmt_error_msg],
      so they'd otherwise get no error message at all (an empty [spec_error] makes the
      checker fail with no reported error, see WISHLIST.md). [rewrite_contract_ext_loop_transfer]
      overrides this default for loop-derived clauses. v1 only supports `Int` (bounded
      below by 0) components; a lexicographic tuple is just a list of such components. *)
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
        let+ specs =
          Rewriter.List.map specs ~f:(fun spec ->
              let+ spec_form =
                type_check_stmt_functs.disambiguate_process_expr spec.Stmt.spec_form Type.int disam_tbl
              in
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
              { spec with Stmt.spec_form; spec_error })
        in
        Decreases specs
    | _ -> Cont.type_check_contract_ext call_decl contract_ext loc disam_tbl type_check_stmt_functs

  (* Rewrites *)
  let rewrite_type_ext = Cont.rewrite_type_ext
  let rewrite_expr_ext = Cont.rewrite_expr_ext
  let rewrite_stmt_ext = Cont.rewrite_stmt_ext

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
      by the call's actual arguments). For Int, "less than" also requires the smaller
      value to be non-negative -- that's what makes Int a well-founded domain here. *)
  let mk_progress_check ~loc (measures_at_entry : expr list) (measures_at_call : expr list) : expr =
    let rec go = function
      | [], [] -> Expr.mk_bool ~loc false
      | e :: entry', c :: call' ->
        let bounded = Expr.mk_app ~loc ~typ:Type.bool Geq [ c; Expr.mk_int ~loc 0 ] in
        let strictly_less = Expr.mk_app ~loc ~typ:Type.bool Lt [ c; e ] in
        let this_component_decreases = Expr.mk_and ~loc [ bounded; strictly_less ] in
        let this_component_equal = Expr.mk_eq ~loc c e in
        let rest = go (entry', call') in
        Expr.mk_or ~loc [ this_component_decreases; Expr.mk_and ~loc [ this_component_equal; rest ] ]
      | _, _ ->
        Error.internal_error loc "decreases: mismatched measure arity between call site and declaration"
    in
    go (measures_at_entry, measures_at_call)

  (** Finds the `decreases` clause (if any) declared on [call_decl], as the raw list of
      per-component specs (in terms of [call_decl]'s own formals). *)
  let find_decreases_measure (call_decl : Callable.call_decl) : Stmt.spec list option =
    List.find_map call_decl.call_decl_contract_ext ~f:(function
      | Decreases specs -> Some specs
      | _ -> None)

  (* Projects the [i]-th lexicographic component back out of the (possibly
     tuple-typed, possibly -- for a single-component clause -- bare `Int`) snapshot
     variable for [call_decl]. [Expr.mk_tuple_lookup] handles both shapes. *)
  let decreases_snapshot_exprs (call_decl : Callable.call_decl) (measures : expr list) : expr list =
    let snap_expr =
      Expr.mk_var ~typ:(decreases_snapshot_type call_decl (List.length measures))
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
           let snap_type = decreases_snapshot_type call_decl (List.length specs) in
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
      (callee_call_decl : Callable.call_decl) (call_args : expr list) (loc : location) :
      Stmt.t list Rewriter.t =
    let open Rewriter.Syntax in
    let own_checks =
      if not (Ident.equal caller_call_decl.call_decl_name callee_call_decl.call_decl_name) then
        (* This hook is now offered every call whose callee has a decreases clause,
           not just recursive ones (core no longer pre-filters -- see
           `rewrite_contract_ext_calls` in rewrites.ml) -- so this check is what
           restricts DecreasesExt's own behavior to Phase 1 scope: only self-recursive
           calls are instrumented. Mutually-recursive calls across distinct callables
           are Phase 2 (WISHLIST) work; an ordinary non-recursive call to a
           decreases-bearing callable is also correctly a no-op here. *)
        []
      else
        match find_decreases_measure caller_call_decl with
        | None -> []
        | Some specs ->
          (* Each [spec]'s own [spec_form] still carries the `decreases ...` clause's
             source location, and its [spec_error] already has the right wording
             (generic, or loop-specific if this clause went through
             [rewrite_contract_ext_loop_transfer]) -- use the first component's for
             the combined lexicographic check, mirroring how failing loop invariants
             are reported (`rewrite_stmt_error_msg`'s [Loop] case, same file): neither
             names the callable currently being checked or points at the call site. *)
          let raw_measures = List.map specs ~f:(fun s -> s.Stmt.spec_form) in
          let spec_error = (List.hd_exn specs).Stmt.spec_error in
          let subst_map =
            List.zip_exn
              (List.map caller_call_decl.call_decl_formals ~f:(fun vd -> QualIdent.from_ident vd.Type.var_name))
              call_args
            |> Map.of_alist_exn (module QualIdent)
          in
          let measures_at_call =
            List.map raw_measures ~f:(fun e -> Expr.alpha_renaming e subst_map)
          in
          let measures_at_entry =
            match caller_call_decl.call_decl_kind with
            | Proc | Lemma ->
              (* Read back the ghost snapshot [rewrite_callable_entry] initialized,
                 since the formals themselves may have been reassigned. *)
              decreases_snapshot_exprs caller_call_decl raw_measures
            | Func | Pred | Invariant ->
              (* Func bodies are pure expressions -- the formals can't be reassigned,
                 so "entry" and "current" always coincide; no snapshot exists (or is
                 needed) for the func case, which piggybacks on the auto-lemma body. *)
              raw_measures
          in
          let check_expr = mk_progress_check ~loc measures_at_entry measures_at_call in
          [ Stmt.mk_assert_expr ~loc
              ~cmnt:"[EXT] DecreasesExt: termination measure must decrease on recursive call"
              ~spec_error
              check_expr
          ]
    in
    let* cont_checks = Cont.rewrite_contract_ext_call caller_call_decl callee_call_decl call_args loc in
    Rewriter.return (own_checks @ cont_checks)

  (* --------------------- *)
  (* --- DO NOT MODIFY --- *)
  let lib_sources = (Option.to_list lib_source) @ Cont.lib_sources
end
