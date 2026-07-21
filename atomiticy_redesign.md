# Atomicity/invariant analysis: soundness bug, related shortcoming, and redesign plan

## 1. Summary of the discussion

### 1.1 The bug

`test/bugs/atomicity_unsound.rav` currently verifies successfully but should not:

```
field f: Int

inv test(x: Ref) {
  own(x.f, 1)
}

proc p(x: Ref, y: Ref)
  requires own(y.f, 1)
  requires test(x)
{
  var z: Ref;
  unfold test(x);
  z := x;
  x := y;
  fold test(x);
  z.f := 3;
}
```

`unfold test(x)` inhales `own(x.f, 1)` while `x` still denotes the caller's original ref. The two local reassignments (`z := x`, `x := y`) are — correctly, in isolation — never treated as atomic/observable steps. But because they are invisible to the invariant bookkeeping, `fold test(x)` at that later point evaluates `x` as `y`'s value, consumes the unrelated `own(y.f, 1)` from the precondition to satisfy it, and never gives back `own(x.f, 1)`. That resource escapes, aliased through `z`, and `z.f := 3` mutates a location still nominally protected by the (never-actually-closed) invariant `test(x)`.

### 1.2 Root cause

Both places that reason about `unfold`/`fold` identify an invariant *instance* by re-evaluating the *source-level argument expression* at each occurrence, instead of by the *value* that expression denoted at the point the invariant was opened:

- `atomicityAnalysis.ml`'s `open_inv`/`close_inv` match invariants via `Expr.alpha_equal` on `inv_args` — literal syntactic comparison, blind to intervening reassignment.
- `rewrites.ml`'s `rewrite_fold_unfold_stmts` independently compiles `unfold`/`fold` to inhale/exhale using `use_desc.use_args`, re-evaluated fresh at each occurrence.
- `Basic (Assign …) -> Rewriter.return stmt` in `atomicityAnalysis.ml` deliberately does not count local reassignment as an atomic step — correct on its own, but it means reassignment is invisible to the matching logic above, letting the same syntactic expression (`x`) silently refer to a different value at `fold`-time than it did at `unfold`-time.

Confirmed empirically: `dune exec -- raven --shh test/bugs/atomicity_unsound.rav` prints `Verification successful.`

### 1.3 A hypothesis raised and refuted along the way

It was initially claimed that `y := x; unfold test(x); unfold test(y);` would also slip through (reentrancy: opening the same instance twice via two different variable names). This was checked directly and is **false**: `open_inv` removes the invariant's *name* (not a per-instance key) from the mask, so a second `unfold` of *any* instance of the same declared invariant — aliased or not — already fails today with `Invariant test is not in the current mask`, independent of the (separately syntactic, and in fact unreachable given this) `already_open`/`alpha_equal` check. Confirmed with a standalone repro. Practical consequence for the redesign: since masks are per-declaration-name, at most one instance of a given invariant name can ever be in `invs_opened` at a time — so "which open instance does this `fold` close" never needs disambiguating by argument matching; only "does it match the *one* open instance" needs checking.

### 1.4 A related but distinct shortcoming: GitHub issue #23

`masks.ml`'s `fixpoint_compute_masks` computes a `Proc`/`Lemma`'s required mask as the flat union of every invariant name *textually mentioned* anywhere in its pre/postconditions, with no distinction between invariants the callable actually *opens* (needs the caller to supply room) versus ones merely *assumed to hold* or *freshly allocated* (fold with no prior unfold). This causes sound programs like issue #23's `create()` (which only allocates a fresh `p(x)` and returns it via `ensures`) to be rejected at call sites whose own spec doesn't happen to mention `p`.

Both issues trace back to the same architectural gap: invariants are tracked as a flat, name-only, syntactic construct with no model of instance identity or provenance (opened-and-must-return vs. freshly-allocated). The unsoundness is the under-approximation face of that gap; issue #23 is the over-approximation face.

### 1.5 Explicitly parked, not part of this redesign

Raven's invariant mask is keyed purely by the fixed declaration name, shared by every instantiation — unlike Iris, where `inv_alloc` picks a dynamically-chosen namespace per allocation, letting two instances of "the same" invariant be opened concurrently when provably disjoint. This is a real expressiveness gap (confirmed: `unfold test(a); unfold test(b)` already fails today for unrelated `a`/`b`), but it is a *different* kind of issue (expressiveness, not soundness) and is tracked separately as its own item in `WISHLIST.md` ("Per-instance invariant namespaces (dynamically-allocated invariant names)"). Not addressed by the plan below.

## 2. Goals / non-goals

**Goals:**
- Part A — fix the `fold`/`unfold` argument-drift unsoundness (§1.1–1.2).
- Part B — fix the mask over-approximation behind issue #23 (§1.4).

**Non-goals:**
- Per-instance/dynamic invariant namespaces (§1.5 / WISHLIST.md).
- Any change to the atomic-update (`au_token`) mechanism. It has the same general shape (an opaque handle compared by `alpha_equal`) but tokens are conventionally bound once via `BindAU` and not reassigned; no concrete bug was found there. Worth a quick standalone audit at some point, but out of scope here unless that audit turns up something.

## 3. Part A: invariant instance identity

### 3.1 Design

Give each *opened* invariant instance a frozen, immutable snapshot of its instantiation arguments, and check the *matching* `fold`'s arguments against that snapshot via an ordinary SMT-discharged equality — replacing the purely syntactic `alpha_equal` comparison, which is what let the drift go unnoticed.

Pass ordering (confirmed by reading `rewrites.ml:process_module`): `rewrites_phase_1` → `Masks.compute_masks` → `rewrites_phase_2` (`rewrite_atomic_callable_token`, then `AtomicityAnalysis.rewrite_atomicity_analysis`) → ext rewrites → `rewrites_phase_3` (`rewrite_add_func_contract_lemmas`, then `rewrite_fold_unfold_stmts`, …). The atomicity analysis runs *before* `rewrite_fold_unfold_stmts` and still sees the original `Use`/`Unfold`/`Fold` statement nodes — the right place to synthesize the new bookkeeping, since it already threads open/close state through the body in one linear walk, and it already synthesizes new statements elsewhere (see `OpenAU`/`AbortAU`/`CommitAU`, which build exhale/inhale blocks the same way).

**Data structure changes (`atomicityAnalysis.ml`):**
- Extend `type invs = { inv_name; inv_args }` to `{ inv_name; inv_args; inv_snapshot : Expr.t }`, where `inv_snapshot` references the fresh ghost variable holding the frozen argument values.
- `open_inv` takes the pre-built snapshot expression (constructed by its caller) and stores it.
- Before closing (in the `Use`/`Fold` handling in `rewrite_au_cmnds`, not inside `close_inv` itself), look up the currently-open entry for `inv_name` to retrieve its `inv_snapshot` — unambiguous, since at most one instance of a given name can be open at once (§1.3).

**Statement synthesis, in `rewrite_au_cmnds`'s `Use` case:**
- On `Unfold`: introduce one fresh ghost local sized to the invariant's own arity, tuple-packed exactly the way `DecreasesExt`'s entry-value snapshot already does (`Type.mk_prod`/`Expr.mk_tuple`, collapsing to a bare type at arity 1 — no tuple wrapper for the common single-argument case), via `Rewriter.introduce_symbol`. Prepend an assignment initializing it to `Expr.mk_tuple use_desc.use_args`, immediately before the (otherwise unmodified) `Use` statement.
- On `Fold`, only when closing a previously-open instance (not a fresh allocation): synthesize a `Stmt.mk_assert_expr` (with a non-empty `~spec_error` — the known pitfall from the `decreases` work: an assert with no spec_error raises an unreported `Msg []`) checking `Expr.mk_eq inv_snapshot (Expr.mk_tuple use_desc.use_args)`, with a message such as "Cannot fold `test`: its arguments no longer match the instance that was opened (a variable used to identify it may have been reassigned)." Insert immediately before the `Use` statement.
- Fresh-allocation folds (no matching open entry) are untouched.

`rewrite_fold_unfold_stmts` itself needs **no changes** — it keeps compiling the (still-present) `Use` node into inhale/exhale of the predicate/body exactly as today. The new assert/assignment are ordinary, independent statements handled by the existing Assert/Assign compilation.

**Effect on the PoC:** the synthesized assert `snapshot == x` (snapshot = original `x`, current `x` = `y`) is unprovable given the preconditions supply no aliasing between them — verification now correctly fails at the `fold` statement.

**Side effect (a relaxation, not just a fix):** a `fold` that closes an instance via a *differently-named but provably-equal* expression (e.g. `unfold test(x); y := x; /* no further reassignment */ fold test(y);`) is rejected today (`alpha_equal` sees different identifiers) but becomes legal, since the check is now semantic. Worth a regression test in the positive direction too.

**Minor cleanup this exposes:** `open_inv`'s `already_open`/`alpha_equal` check is dead code given per-name mask granularity (§1.3) — the mask-membership check alone already rejects any second open of the same name. Can be left as defense-in-depth/documentation of intent, or removed; not required either way.

### 3.2 Deferred (not required for soundness): a static "borrow" guard

Tracking the free variables of each open invariant's `inv_args` (via the existing `Expr.signature`/`Expr.local_vars`) and rejecting `Assign`/`Havoc`/`Bind` to any of them while open would catch the PoC earlier — at the `x := y` statement — with a clearer, more localized message. It is **not** needed for soundness: the semantic snapshot-equality assert in §3.1 already rejects the PoC on its own (just later, at the `fold`). Recommend treating this as a follow-up diagnostic-quality improvement rather than bundling it into the initial fix.

### 3.3 Implementation steps

1. Extend the `invs` record and `open_inv`/`close_inv`-adjacent plumbing in `atomicityAnalysis.ml` (structural change, no behavior change yet).
2. Implement snapshot introduction on `Unfold` (fresh ghost local + assignment synthesis).
3. Implement snapshot lookup + equality-assert synthesis on `Fold`'s closing case.
4. `dune runtest`; expect zero regressions (a syntactically-unchanged argument trivially satisfies the new equality check) — verify rather than assume, and investigate any surprise.
5. Confirm `test/bugs/atomicity_unsound.rav` now fails to verify, with the new assert's message at the `fold` site.
6. Migrate it into a proper cram test under `test/ci/back-end/fail/` and remove it from `test/bugs/` (matching the existing project convention — `test/bugs/` holds unfixed repros only; cf. the "eliminate, now obsolete bug test case" precedent already in the git history).
7. Add a positive test for the newly-legal alias-fold case (§3.1, "side effect").

## 4. Part B: mask over-approximation (issue #23)

### 4.1 Refined diagnosis

Two separate over-approximations compound the problem:
1. `masks.ml` derives `call_decl_mask` for `Proc`/`Lemma` from a **spec-level** scan (names mentioned in `requires`/`ensures`), rather than from what the callable's **body** actually does.
2. `close_inv`'s "folding a new invariant" branch requires the invariant's name to already be in the mask before a *fresh allocation* is even allowed — but allocating a brand-new instance shouldn't need or touch mask availability at all; only *opening* (`unfold`) an already-existing instance should. (This matches real Iris: a mask/namespace only shrinks on `inv_open`, and is untouched by `inv_alloc`.) This requirement is itself an unforced, overly conservative choice baked into the current implementation, not an inherent necessity.

### 4.2 Proposed direction

1. Drop the mask-membership requirement from `close_inv`'s fresh-allocation branch — allocation never checks or consumes mask.
2. Recompute `call_decl_mask` for `Proc`/`Lemma` from a **body-level, sequencing-aware** walk: the set of invariant names the body ever `unfold`s — directly, or transitively via the `call_decl_mask` of callables it calls — **excluding** any name the same body has already fold-*allocated* on every path reaching that `unfold` (self-provided, doesn't need to come from the caller). This is effectively a variant of `AtomicityAnalysis`'s own traversal, run in an "inference" mode against an initially-unconstrained mask, rather than an unordered textual scan.
3. Leave the `Pred | Invariant` branch of `fixpoint_compute_masks` (nested-invariant-body scanning) unchanged — that is a deliberate, still-appropriate static over-approximation of what a caller might need if it goes on to unfold a nested invariant; it isn't part of the bug.

### 4.3 Open design questions — flagged, not resolved

These need a short dedicated review before coding starts on Part B; §4.2 is a direction, not yet a fully specified algorithm:

- **Starting-mask model.** Should a callable's *own* starting mask for verifying its body conceptually be ⊤ (all declared invariants, since Raven verifies each callable once, modularly, not per call site), with `call_decl_mask` demoted to a pure call-site precondition — rather than today's design, where `call_decl_mask` doubles as both the call-site precondition *and* the literal starting mask used to check the callable's own body? Changing this changes what "correct" means for step 2 above.
- **Does a caller ever gain durable mask credit from a call?** E.g. after `val x := create()`, can `foo` now `unfold p(x)`, or was `p` already unconditionally available to `foo` under the corrected (allocation-doesn't-touch-mask) model? Working hypothesis from the discussion: under the corrected model a callable's *net* effect on its caller's mask is always zero, because everything it opens it must reclose before returning (already enforced) and allocation no longer touches mask at all — so no explicit "credit propagation" step should be needed at call sites. This is exactly the kind of point that's easy to get backwards; confirm with a small, deliberately adversarial test matrix (see §4.4 step 2) before committing.
- **Interaction with mutual recursion / SCCs.** The `decreases`-clause work (WISHLIST.md) already built SCC infrastructure (`lib/ast/callGraph.ml`) for exactly this kind of body-level, call-graph-fixpoint computation. Check whether it can be reused directly for the mask fixpoint rather than re-deriving it.

### 4.4 Implementation steps — first cut, expect revision after §4.3

1. Remove the mask-membership check from `close_inv`'s fresh-allocation branch.
2. Before committing to the general algorithm, prototype the body-level "required mask" computation against a couple of hand-picked cases: the issue #23 repro, and a deliberately adversarial one (a callable that allocates `P` and *later* also needs to open a different, caller-supplied instance of `P`) — this is precisely where §4.3's open questions bite.
3. Replace the `Proc | Lemma` branch of `masks.ml`'s `fixpoint_compute_masks` with the new body-based computation; leave `Pred | Invariant` untouched.
4. `dune runtest`; this change should only ever make the check *more* permissive, so investigate any regression as a correctness bug in the new computation, not an expected fallout.
5. Add the issue #23 repro and the adversarial case from step 2 as new cram tests under `test/ci/back-end/`.
6. Revisit `test/ci/back-end/fail/masks_1.rav`: confirm whether its expected failure should change under the new model (it may now legitimately verify, or may still fail for a different, correct reason) before touching its expected `.t` output — `dune promote` only after confirming the new behavior is actually correct, not merely different.

## 5. Suggested sequencing

Land Part A first, as its own change: it directly closes a confirmed soundness hole, and the design in §3 is fully specified with no open questions. Treat Part B as a separate follow-on effort, since §4.3's open questions warrant a short dedicated design pass before implementation starts, rather than being resolved opportunistically while coding.
