# 5d. Automation Features

All three capstones you just finished were quietly leaning on a handful of smaller features that
make Raven's automation more usable in practice. None of them are new *reasoning* — everything
here is still ownership, invariants, and resource algebras from Parts 2–4 — they're ergonomics.
Code for the first and last sections is in [`automation.rav`](./automation.rav); the middle two
are already demonstrated in place by 5a–5c, and cited rather than duplicated.

## Implicit parameters

```raven
pred sized(c: Ref; n: Int) {
  own(c.count, n) && n >= 0
}
```

Compare this to Part 3's `pred valid(c: T, v: Int)`, where `v` was an ordinary, explicit
parameter: every call site had to spell it out — `valid(c, v)`, `fold valid(c, v)`. Here, `n` is
separated from `c` by a **semicolon**, marking it implicit: [`automation.rav`](./automation.rav)'s
`peek` and `create` both write just `sized(c)`, everywhere, and Raven recovers `n` on its own
from whatever `sized(c)` resource is already in scope.

This isn't just sugar — Raven checks a real side condition to make it sound: it must be
impossible to simultaneously hold `sized(c, n1)` and `sized(c, n2)` for `n1 != n2`. (Part 3's
`Sum` functor exercise deliberately used explicit ghost parameters instead of implicit ones for
exactly this reason — introducing the uniqueness side condition alongside the existential-witness
machinery in the same exercise would have been one new idea too many at the time.)

## Implicit ghost parameters, for procs and lemmas

A `proc` or `lemma` parameter can be marked implicit the exact same way — every atomic-contract
signature in 5b (`implicit ghost r: R`) and 5a's `Instance` interface already lean on this — but
without `pred`'s uniqueness side condition, because there's nothing to be ambiguous about here.
`sized`'s `n` has to be *searched for*, since `sized(c)` is an opaque, foldable resource that
could in principle be witnessed by more than one value unless Raven separately checks otherwise.
[`automation.rav`](./automation.rav)'s `nonNegCount` is different: its implicit `n` is recovered
from an ordinary, already-visible `own` fact directly — whatever value that fact already holds
*is* `n`, by plain unification, nothing to prove unique first:

```raven
lemma nonNegCount(c: Ref, implicit ghost n: Int)
  requires own(c.count, n, 1.0) && n >= 0
  ensures own(c.count, n, 1.0)
{
}
```

Calling `nonNegCount(c)` right after `unfold sized(c)` recovers `n` from the `own` fact the
unfold just produced — no search, no uniqueness proof, just reading off a value that's already
sitting there in plain sight.

## Witness computation

When you `fold`/`unfold` a predicate or invariant whose body existentially quantifies over some
variables — `shelfInv`'s `counts`, `lock_inv`'s `n`/`c`/`b` in 5b, `is_forkjoin`'s `o`/`b` in 5a
— Raven tries to work out a witness for each existential from the surrounding proof state
automatically, rather than leaving it to the solver as an opaque quantifier. This is exactly what
let `shelf_of_counters.rav`'s `bump` write `fold shelfInv(s)[counts := counts[i := counts[i] +
1]]` and have every *other* index's value inferred, rather than requiring you to spell out the
whole map. The same witness computation heuristic also works for implicit arguments of invariants
and predicates as Raven ensures that these are uniquely determined by the non-implicit
arguments. When no heuristic applies — most often, when a witness genuinely isn't determined by
anything else you already own — you supply it explicitly, exactly the way
`ticket_lock_invariant.rav`'s `fold lock_inv(l, r)[b := lockAcq]` supplies `b` by hand while
leaving `n`/`c` to be inferred.

## `auto` lemmas and predicates

Two related but different uses of `auto`:

- An **`auto lemma`/`auto axiom`** doesn't need to be invoked with an explicit ghost statement —
  Raven asserts it automatically wherever a term it mentions appears. `shelf_of_counters.rav`'s
  `all_diff` is one (even though this tutorial calls it explicitly anyway, as a small defensive
  habit, not because it's required). Because it's asserted unconditionally, everywhere it
  applies, its entire `requires`/`ensures` has to be **pure** — no `own`, no calling a `pred` or
  `proc`, nothing that inspects or manipulates a resource — Raven rejects an `auto lemma` whose
  contract isn't (`This specification of auto lemma %s is not pure`). This is a hard boundary,
  not just a style guideline: there's no such thing as an `auto` lemma about ownership.
- An **`auto pred`** is automatically inlined wherever it's used. No `fold`/`unfold` is ever
  needed, unlike every predicate you've seen so far. 5a's fork/join capstone is built entirely
  around watching this happen: `fork_join_explicit.rav`'s plain `pred token` needs an explicit
  proof for `token_unique` and an explicit call to it inside `join`; marking `token` `auto` in
  `fork_join.rav` is the *only* change that shrinks the lemma's proof to an empty body and
  deletes the explicit call entirely, since `token(p) && token(p)` now expands to the same
  contradiction on its own, with nobody asking it to. If §6 of that capstone didn't fully land,
  it's worth a second look now with this framing in mind.
  [`ticket_lock_atomic.rav`](../atomic-contracts/ticket_lock_atomic.rav)'s `locked` uses exactly
  the same trick, for exactly the same reason, on a different `Excl`-flavored algebra.

  The trade-off: an `auto pred` saves you the fold/unfold bookkeeping for something simple, at
  the cost of handing the solver a bigger, unfolded formula to reason about every time it appears
  — fine for a one-line body like `token`'s or `locked`'s, potentially costly for something
  bigger. Also, since `auto` predicates unfold automatically, they cannot be recursive.

## Triggers, revisited

Part 1 introduced trigger annotations `{...}` for quantifiers as "a hint for the SMT solver,
don't worry about it yet." Now that you've written a few: a trigger tells the SMT solver *which*
terms should cause it to re-instantiate a quantified fact (a technique called E-matching). Every
`{S.loc(s, i)}` in `shelf_of_counters.rav` is doing this — without it, the solver has no
principled way to decide *when* to bring the ISC's per-index fact into play, and either
instantiates it too rarely (proofs that should go through, don't) or too eagerly (see the
Debugging Corner below). ISCs are a natural place to see triggers for the first time, since Raven
requires one there, but they're not really an ISC-specific idea — the more common case where
you'll actually need to write one by hand is an ordinary *pure* quantified fact (an axiom or
lemma postcondition over some uninterpreted function), the same way `Bounds`'s `lowHigh` does in
`automation.rav`, below.

A trigger can name more than one term, comma-separated — `{low(x), high(y)}` only fires once
*both* terms already appear, together, as ground terms somewhere in the current proof state.
Between the whole set, every bound variable has to be covered, but no single term needs to
mention all of them alone. A quantifier can also carry more than one trigger *set*, written back
to back — `{t1} {t2}` — meaning either set firing on its own is enough to trigger the
instantiation, independently of the other:

```raven
interface Bounds {
  func low(x: Int) returns (r: Int)
  func high(x: Int) returns (r: Int)

  auto axiom lowHigh()
    ensures forall x: Int, y: Int :: {low(x), high(y)} x < y ==> low(x) <= high(y)
}
```

`test/arrays/array_utils.rav` and `test/concurrent/templates/flows_ra.rav` both use several
trigger sets on a single quantifier at once, for facts considerably less tidy than this one — a
good next stop once this shape feels familiar. A trigger, whichever shape it takes, should
mention every bound variable of its quantifier (across the whole set, for a multi-term one) and
pick a term that actually appears in contexts where you need the fact instantiated. Importantly,
the trigger terms will be matched modulo equalities derivable by the solver (that's the "E" in
E-matching). E.g., if the ground term `f(g(a), c)` is in the proof context, the trigger term is
`f(x,b)` and the solver derives `c == b`, then `x` will be instantiated with `g(a)`. So be aware
that ground terms don't always need to match literally in order to trigger a quantifier
instantiation.

## `assert ... with`

For a universally-quantified *pure* assertion `a`, the statement `assert a with { s }` lets you
pick an arbitrary value of the bound variable, run `s` against it, and construct a specific
proof, rather than leaving the whole `forall` to the solver's own automation — inside the `with`
block, Raven havocs the bound variable, runs `s`, and checks the body holds; the `forall` itself
is then simply assumed for everything that follows, the same as any ordinary `assert`. It earns
its keep specifically when proving the body `P(x)` of `forall x: T :: P(x)` needs an explicit
lemma call for each individual `x` — not something Z3 can already do unaided:

```raven
func sumUpTo(n: Int) returns (s: Int)
  decreases n
{
  n <= 0 ? 0 : n + sumUpTo(n - 1)
}

lemma sumFormula(n: Int)
  ensures n >= 0 ==> sumUpTo(n) * 2 == n * (n + 1)
  decreases n
{
  if (n > 0) {
    sumFormula(n - 1);
  }
}

proc demoAssertWith()
{
  assert forall n: Int :: n >= 0 ==> sumUpTo(n) * 2 == n * (n + 1) with {
    sumFormula(n);
  }
}
```

`sumFormula` establishes the closed-form sum by induction, one call per `n`; the `assert ...
with` is what turns "true for whichever specific `n` I happen to call `sumFormula` with" into a
genuine quantified fact the rest of a proof can use without calling it again. This isn't a
demonstration fact that the SMT solver could already manage alone — delete the `with` block (or
just the `sumFormula(n);` call inside it) and the `assert` fails on its own: proving a
closed-form identity by induction is exactly the kind of reasoning the solver can't discover by
itself, which is the whole reason this construct exists. `test/arrays/array_utils.rav`'s own real
uses of it (cited from `automation.rav`'s comments) go a step further still, extracting a witness
via `:|` (bind) partway through the `with` block and reasoning from it directly.

## Debugging Corner: "my proof just hangs"

This is the one failure mode with no diagnostic to read at all. The status bar spins, or the
check eventually times out, and — unlike every earlier Debugging Corner — there's no message
pinpointing *why*: that would require solver internals (which quantifier got instantiated how
many times, against which trigger) that are deliberately out of scope for this tutorial's
target reader. So what follows is a checklist of *moves*, not messages to interpret. After each
one, re-run "Raven: Verify File" to see whether it helped:

- **Strip candidate quantified facts out one at a time.** If a proof was fast before you added a
  `forall`/`exists` somewhere, and slow after, that's your suspect — regardless of how
  unrelated it looks.
- **Add an explicit trigger to any `forall` you just introduced**, especially one over a `Map`
  or function application, and see if that alone fixes it. A missing or *too permissive* trigger
  (one that matches all over the place) tends to cause "too slow"; a *too restrictive* one (one
  that never quite matches what's actually in scope) tends to cause "doesn't get instantiated at
  all" — opposite symptoms, same fix, so try adjusting the trigger either way rather than
  assuming which direction is wrong. Watch out for *matching loops* too — sometimes called
  trigger loops — where a trigger's own instantiation produces a new ground term that matches
  that same (or another) trigger again, so the solver keeps re-firing it without ever converging; this is a
  well-documented phenomenon across the whole family of SMT-backed verifiers (Dafny, Boogie,
  F*), worth searching for by that name if a proof hangs no matter what else you try here.
- **Split a large procedure's proof into a separate `lemma`.** Each piece then gets checked (and
  reported on) independently, instead of as one large, opaque combined query — this also makes
  the *previous* two techniques much easier to apply, since you're now searching a smaller
  space.

You won't always find out *why* something was slow, and that's fine — the goal here is learning
what tends to make Raven's automation struggle, so you can avoid triggering it, not diagnosing
it forensically after the fact.

## What's next

You've now seen everything this tutorial set out to cover — Appendix A works through resource
algebras' formal definition for readers who want the Part 4 constructions justified rather than
motivated; Appendix B is a quick dictionary for readers coming from Viper, Dafny, or Iris;
Appendix C points at the Extension API for readers who want to add new front-end syntax rather
than just write proofs; Appendix D has pointers to more worked examples than this tutorial
itself covers.
