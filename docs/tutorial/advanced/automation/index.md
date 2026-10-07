# 5.5. Automation Features

All four capstones you just finished relied on a handful of smaller features that make Raven's
automation more usable in practice. None of them introduce new *reasoning*. Everything here is
still the ownership, invariants, and resource algebras from Parts 2–4. These features just make
them more convenient to use. Code for the first and last sections is in
[`automation.rav`](./automation.rav). The middle ones are already demonstrated in 5.1–5.4, and
are cited rather than duplicated.

## Implicit parameters {#sec:implicit-parameters}

```raven
pred sized(c: Ref; n: Int) {
  own(c.count, n) && n >= 0
}
```

Compare this to Part 3's `pred valid(c: T, v: Int)`, where `v` was an ordinary, explicit
parameter that every call site had to spell out, as in `valid(c, v)` and `fold valid(c, v)`.
Here, `n` is separated from `c` by a **semicolon**, which marks it as implicit. In
[`automation.rav`](./automation.rav), `peek` and `create` both write just `sized(c)` everywhere,
and Raven recovers `n` on its own from whatever `sized(c)` resource is already in scope.

This is more than syntactic sugar. To make it sound, Raven checks a real side condition: it must
be impossible to simultaneously hold `sized(c, n1)` and `sized(c, n2)` for `n1 != n2`. (Part 3's
`Sum` functor exercise deliberately used explicit ghost parameters instead of implicit ones for
exactly this reason. Introducing the uniqueness side condition together with the
existential-witness machinery in the same exercise would have been one new idea too many at that
point.)

## Implicit ghost parameters, for procs and lemmas {#sec:implicit-ghost-parameters}

A `proc` or `lemma` parameter can be marked implicit in the same way. Every atomic-contract
signature in 5.2 (`implicit ghost r: R`) and 5.1's `Instance` interface already rely on this.
Here, however, there is no uniqueness side condition like the one for `pred`, because there's
nothing ambiguous. `sized`'s `n` has to be *searched for*, since `sized(c)` is an opaque, foldable
resource that could in principle be witnessed by more than one value unless Raven separately
checks otherwise. The lemma `nonNegCount` in [`automation.rav`](./automation.rav) is different.
Its implicit `n` is recovered directly from an ordinary, already-visible `own` fact. Whatever
value that fact holds *is* `n`, by plain unification, so there is nothing to prove unique first:

```raven
lemma nonNegCount(c: Ref, implicit ghost n: Int)
  requires own(c.count, n, 1.0) && n >= 0
  ensures own(c.count, n, 1.0)
{
}
```

Calling `nonNegCount(c)` right after `unfold sized(c)` recovers `n` from the `own` fact that the
unfold just produced. There is no search and no uniqueness proof. Raven simply reads off a value
that is already visible.

## Witness computation {#sec:witness-computation}

When you `fold` a predicate or invariant whose body existentially quantifies over some variables
(`shelfInv`'s `counts`, `lock_inv`'s `n`/`c`/`b` in 5.2, `is_forkjoin`'s `o`/`b` in 5.1), you're
*proving* that existential. Some concrete value is already implied by the surrounding proof state
(for instance, the value you just wrote to a field), and folding has to establish that the body
holds for it. Raven tries to work out that witness automatically rather than leaving it to the
solver as an opaque quantifier. This is what allowed `bump` in `shelf_of_counters.rav` to write
`fold shelfInv(s)[counts := counts[i := counts[i] + 1]]` and have the value at every *other*
index inferred, rather than requiring you to spell out the whole map. The same heuristic also
works for implicit arguments of invariants and predicates, since Raven ensures that two instances
held at the same time agree on them if they agree on the explicit arguments. When no heuristic
applies (most often because a witness isn't determined by anything else you already own), you
supply it explicitly. For
example, `fold lock_inv(l, r)[b := lockAcq]` in `ticket_lock_invariant.rav` supplies `b` by hand
while leaving `n`/`c` to be inferred. In natural-deduction terms, this whole section is about
automated **existential introduction**. You (usually implicitly) already have a specific witness
in hand, and Raven's job is to prove that the body holds for it.

## The bind statement (`x :| ...`) {#sec:bind-statement}

`:|` is the dual of witness computation, not another name for it. Folding *proves* an
existential by supplying a witness. In contrast, `:|` (read "bind" or "such that") starts from an
existential that is *already known to hold* and gives you a handle on a witness to reason with,
without committing to which one. In natural-deduction terms, this is **existential elimination**,
the same step as Skolemization. From `∃x. P(x)`, you introduce a fresh name `x` standing for an
arbitrary value satisfying `P`, and reason from `P(x)` onward, without ever learning (or needing
to learn) which value `x` actually is. You've already seen this in Part 4, where `bump` in
`hit_counter_ghost.rav` writes

```raven
ghost var v2: Int
unfold countInv(c)
v2 :| own(c.count, v2, 1.0)
```

`v2 :| own(c.count, v2, 1.0)` reads as "bind `v2` to some value such that `own(c.count, v2, 1.0)`
holds." Since `countInv` was just unfolded, exactly one such value exists (the current value of
`count`), so this stores it in `v2` without having to name it any other way.

Under the hood, `x :| P;` consists of two steps in sequence. Both are worth knowing about
separately, because they fail differently. First, Raven checks `exists x :: P`, confirming the
premise that elimination needs, namely that such an `x` really exists. Raven doesn't carry an
explicit proof term for this the way a natural-deduction derivation would. It just re-checks the
premise with the solver at the `:|`, like any other assertion. Normally this step is almost free,
since `P` is usually exactly (or derived from) an existential you already hold, like
`own(c.count, v2, 1.0)` here, which comes straight out of the `unfold`. Still, it's a real proof
obligation, and if it can't be discharged, you get `[Verification Error] The right-hand side of
this bind statement may not hold`. Second, once that premise is confirmed, the elimination itself
happens. Raven treats `x` as freshly bound to *some* value satisfying `P`. It doesn't matter
which, and a repeated `:|` on the same variable forgets whatever value it held before, just as
reassigning a `var` does. The left-hand side can list more than one variable, separated by commas
(`x, y :| P`), extracting a joint witness for all of them from a single proposition.

The first step is easy to underestimate, because it's tempting to read `:|` as "the compiler
will find one for me" rather than "the solver has to prove that one exists." It's an ordinary SMT
proof obligation, not an oracle. As with the induction hypotheses of `assert ... with`, the
solver doesn't search arbitrarily hard for a witness on its own.
[`broken/bind_unprovable.rav`](./broken/bind_unprovable.rav) binds two variables at once to a
proposition that's true (`x = 10, y = 0` is one of many witnesses) but not easy for the solver:

```raven
ghost var x: Int
ghost var y: Int
x, y :| x + y == 10 && x >= 0 && y >= 0
```

This fails with exactly the "right-hand side... may not hold" error above, even though the fact
is true. Compare this to Part 4's `v2 :| own(c.count, v2, 1.0)`. There, the witness appears
directly in an `own` fact that is already in scope, so it is essentially handed to the solver
rather than searched for. A `:|` proposition works reliably when it has this form (a direct
equality, or a fact already visible in the current proof state), rather than being a compound
arithmetic condition for which the solver would have to invent a witness from nothing.

Finally, there's a connection to {{ref sec:ghost-blocks-erasure}} worth making explicit. `:|`
is inherently a *ghost* statement, regardless of which scope it's written in, because a value
chosen this way ("some value satisfying `P`, whichever one") must never influence the compiled
program's real behavior. Concretely, this means that the bound variable itself must be a
`ghost var` (or a `ghost`/`implicit ghost` parameter). Binding into a plain, non-ghost `var` runs
into the same check that {{ref sec:ghost-blocks-erasure}} introduced for writing real state from
ghost code, `[Type Error] Cannot assign to non-ghost var x in ghost context`, because from the
type checker's point of view, that's exactly what such a `:|` would be doing.

## `auto` lemmas and predicates {#sec:auto-lemmas-predicates}

There are two related but different uses of `auto`:

- An **`auto lemma`/`auto axiom`** doesn't need to be invoked with an explicit ghost statement.
  Raven asserts it automatically wherever a term it mentions appears. `all_diff` in
  `Library.Array`, on which `shelf_of_counters.rav` relies, is one example. Because it's asserted
  unconditionally
  wherever it applies, its entire `requires`/`ensures` has to be **pure**. That means no `own`, no
  calls to a `pred` or `proc`, and nothing that inspects or manipulates a resource. Raven rejects
  an `auto lemma` whose contract isn't pure (`This specification of auto lemma %s is not pure`).
  This is a hard rule, not just a style guideline. There's no such thing as an `auto` lemma about
  ownership.
- An **`auto pred`** is automatically inlined wherever it's used. Unlike every predicate you've
  seen so far, it never needs a `fold`/`unfold`. 5.1's fork/join capstone is built around
  demonstrating this. In `fork_join_explicit.rav`, the plain `pred token` needs an explicit
  proof for `token_unique` and an explicit call to it inside `join`. Marking `token` as `auto` in
  `fork_join.rav` is the *only* change needed to shrink the lemma's proof to an empty body and
  remove the explicit call entirely, since `token(p) && token(p)` now expands to the same
  contradiction on its own, without being asked. If {{ref sec:auto-predicates}} wasn't entirely
  clear, it's worth a second look now with this framing in mind. `locked` in
  [`ticket_lock_atomic.rav`](../atomic-contracts/ticket_lock_atomic.rav) uses exactly the same
  trick, for the same reason, with a different `Excl`-like algebra.

  There is a trade-off. An `auto pred` saves you the fold/unfold bookkeeping for something
  simple, at the cost of handing the solver a bigger, unfolded formula every time it appears.
  That's fine for a one-line body like `token` or `locked`, but potentially costly for something
  bigger. Also, since `auto` predicates unfold automatically, they cannot be recursive.

## Triggers, revisited {#sec:triggers-revisited}

Part 1 introduced trigger annotations `{...}` for quantifiers as "a hint for the SMT solver,
don't worry about it yet." Now that you've written a few, here's a closer look. A trigger tells
the SMT solver *which* terms should cause it to instantiate a quantified fact (a technique called
E-matching). Every `{loc(s, i)}` in `shelf_of_counters.rav` does this. Without it, the solver
has no principled way to decide *when* to bring the ISC's per-index fact into play. It would
either instantiate it too rarely (so that proofs that should go through don't) or too eagerly
(see the Debugging Corner below). ISCs are a natural place to encounter triggers for the first
time, since Raven requires one there, but triggers are not specific to ISCs. The more common case
where you'll need to write one by hand is an ordinary *pure* quantified fact (an axiom or lemma
postcondition over some uninterpreted function), like `lowHigh` in `Bounds` in
`automation.rav`, shown below.

A trigger can name more than one term, separated by commas. For example, `{low(x), high(y)}`
only fires once *both* terms appear as ground terms somewhere in the current proof state.
Together, the terms in the set have to cover every bound variable, but no single term needs to
mention all of them. A quantifier can also carry more than one trigger *set*, written one after
the other as in `{t1} {t2}`. This means that either set is enough on its own to trigger the
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
trigger sets on a single quantifier, for facts that are considerably messier than this one. They
are good examples to look at once this pattern feels familiar. Whatever form it takes, a trigger
should mention every bound variable of its quantifier (across the whole set, for a multi-term
trigger) and use terms that actually appear in contexts where you need the fact instantiated.
Importantly, the trigger terms are matched modulo equalities that the solver can derive (that's
the "E" in E-matching). For example, if the ground term `f(g(a), c)` is in the proof context, the
trigger term is `f(x,b)`, and the solver derives `c == b`, then `x` will be instantiated with
`g(a)`. So be aware that ground terms don't always need to match literally to trigger a
quantifier instantiation.

## Inline functions {#sec:inline-functions}

A `func` with a body normally reaches the SMT solver as an uninterpreted function, together with
an axiom saying that each application equals the body. The solver instantiates that axiom when an
application turns up in the proof, much like the quantified facts above. Declaring the function
`inline` instead makes its body a macro: every application is replaced by the body before the
solver sees it.

```raven
inline func union(s: Set[Int], t: Set[Int]) returns (r: Set[Int]) {
  {| x: Int :: x in s || x in t |}
}
```

This pays off when the solver can reason about the body directly. Here, the body combines `s` and
`t` element by element, which Raven passes on as an operation on whole sets that the solver
handles natively, so `unionAssoc` in [`automation.rav`](./automation.rav) needs no proof. In a
large proof, unfolding every application through its axiom instead can be the difference between
a quick result and a timeout.

`inline` is only a hint. It is ignored for a recursive function, whose unfolding would never end.
And since the body replaces every application, including those in triggers, don't use an inline
function in a trigger: the trigger would consist of the body, which is generally not a term the
solver can match.

## `assert ... with` {#sec:assert-with}

For a universally quantified *pure* assertion `a`, the statement `assert a with { s }` lets you
pick an arbitrary value of the bound variable, run `s` on it, and construct a specific proof,
rather than leaving the whole `forall` to the solver's automation. Inside the `with` block, Raven
havocs the bound variable, runs `s`, and checks that the body holds. The `forall` itself is then
assumed for everything that follows, as with any ordinary `assert`. This construct is useful
specifically when proving the body `P(x)` of `forall x: T :: P(x)` requires an explicit lemma
call for each individual `x`, which Z3 can't do unaided:

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

`sumFormula` establishes the closed-form sum by induction, with one call per `n`. The `assert ...
with` turns "true for whichever specific `n` I happen to call `sumFormula` with" into an actual
quantified fact that the rest of a proof can use without calling the lemma again. The SMT solver
could not prove this fact on its own. If you delete the `with` block (or just the
`sumFormula(n);` call inside it), the `assert` fails. Proving a closed-form identity by induction
is exactly the kind of reasoning that the solver can't discover by itself, which is why this
construct exists. `test/arrays/array_utils.rav` (cited in the comments of `automation.rav`) uses
it in the same way: lemmas proved by induction establish facts about one map at a time, and
`assert ... with` turns them into the quantified `auto` lemmas the rest of the file relies on.

## Debugging Corner: "my proof just hangs"

This is the one failure mode with no diagnostic to read at all. The status bar spins, or the
check eventually times out. Unlike in every earlier Debugging Corner, there's no message
pinpointing *why*. That would require looking at solver internals (which quantifier got
instantiated how many times, against which trigger), which are deliberately out of scope for
this tutorial's intended audience. So what follows is a checklist of *things to try*, not
messages to interpret. After each one, re-run "Raven: Verify File" to see whether it helped:

- **Strip candidate quantified facts out one at a time.** If a proof was fast before you added a
  `forall`/`exists` somewhere, and slow after, that's your suspect, regardless of how
  unrelated it looks.
- **Add an explicit trigger to any `forall` you just introduced**, especially one over a `Map`
  or function application, and see if that alone fixes it. A missing or *too permissive* trigger
  (one that matches all over the place) tends to make things too slow. A *too restrictive* one
  (one that never quite matches what's actually in scope) tends to mean the fact doesn't get
  instantiated at all. The symptoms are opposite but the fix is the same, so try adjusting the
  trigger in either direction rather than assuming which one is wrong. Also watch out for
  *matching loops* (sometimes called trigger loops). In a matching loop, instantiating a trigger
  produces a new ground term that matches the same (or another) trigger again, so the solver
  keeps firing it without ever converging. This is a well-documented phenomenon across the whole
  family of SMT-backed verifiers (Dafny, Boogie, F*), and it's worth searching for by that name if
  a proof hangs no matter what else you try here.
- **Split a large procedure's proof into a separate `lemma`.** Each piece then gets checked (and
  reported on) independently, instead of as one large, opaque combined query. This also makes
  the *previous* two techniques much easier to apply, since you're now searching a smaller
  space.

You won't always find out *why* something was slow, and that's fine. The goal is to learn what
tends to make Raven's automation struggle so that you can avoid it, not to diagnose every
slowdown in detail after the fact.

## What's next

You've now seen everything this tutorial set out to cover. The appendices provide additional
material:

- {{ref app:resource-algebras}} works through the formal definition of resource algebras,
  for readers who want the Part 4 constructions justified rather than just motivated.
- {{ref app:hardware-primitives}} shows how to add an atomic hardware primitive that the
  standard library doesn't provide, without touching the verifier.
- {{ref app:stdlib-types}} describes the data types of the standard library that the main
  tutorial doesn't use: options, lists, sequences, and arrays.
- {{ref app:from-other-tools}} is a quick dictionary for readers coming from Viper, Dafny, or
  Iris.
- {{ref app:extension-api}} points to the Extension API, for readers who want to add new
  front-end syntax rather than just write proofs.
- {{ref app:where-next}} has pointers to more worked examples than this tutorial covers.
