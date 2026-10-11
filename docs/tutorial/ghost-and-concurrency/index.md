# 4. Ghost Code and Basic Concurrency

This is the part where Raven stops looking like a sequential program verifier and starts doing
what it's actually designed for. Everything from Parts 1–3 (ownership, fractional permissions,
the frame rule, modules) was building toward reasoning about a heap that more than one thread can
access at once. There are two main companion files.
[`hit_counter_invariant.rav`](./hit_counter_invariant.rav) covers
{{ref sec:threads-and-atomics}}–{{ref sec:shared-invariants}}, without any ghost state yet.
[`hit_counter_ghost.rav`](./hit_counter_ghost.rav) covers
{{ref sec:ghost-fields-resource-algebras}}–{{ref sec:frame-preserving-updates}}, where ghost
fields and resource algebras enter. In addition, there are a couple of small standalone files for
{{ref sec:ghost-blocks-erasure}}, which is about the ghost/non-ghost boundary itself:
[`ghost_scope.rav`](./ghost_scope.rav) and [`ghost_steps.rav`](./ghost_steps.rav).

## Threads and atomic primitives {#sec:threads-and-atomics}

```raven
proc bumpTwice(c: Ref)
  requires evenCount(c)
{
  unfold evenCount(c)
  val _x := faa(c.count, 2)
  fold evenCount(c)
}
```

The statement `spawn p(args)` calls procedure `p` running as a new, independent thread. The
statement terminates immediately after the new thread has been created. It does not wait for
`p` to terminate. `faa` (fetch-and-add) is one of the *atomic* heap operations the standard
library provides, brought into scope by the `import Library.IntAtomics._` at the top of the
file. The call in the example is equivalent to `c.count := c.count + 2` but the
read-and-increment of `c.count` happens as a single indivisible step. These operations are not
built into the language. They are ordinary procedures, and a hardware primitive that the library
does not provide can be written in the same way. In Raven, a data race isn't something a separate
tool has to hunt for after the fact. It shows up as a proof that fails to go through, for reasons
that the next section makes concrete.

## The problem shared invariants solve {#sec:shared-invariants-problem}

Consider [`broken/no_invariant.rav`](./broken/no_invariant.rav):

```raven
proc client() returns (c: Ref)
{
  c := create()
  spawn increment(c) // Part 2's ownership-transfer `increment`
  spawn increment(c)
}
```

This fails immediately with `[Verification Error] A precondition may not hold for this call` on
the *second* `spawn`. The first `spawn` already consumed the one full permission that `create`
produced, so there is nothing left to hand to the second thread. This makes the limitation
concrete. Part 2's resource-transfer model has no way to express "many threads share access to
this cell, provided each one's own step leaves it in a good state." It can only express "one
owner has it, then hands it fully to the next." Shared invariants fill exactly this gap.

## Shared invariants {#sec:shared-invariants}

```raven
inv evenCount(c: Ref) {
  exists v: Int :: own(c.count, v) && v % 2 == 0
}
```

An `inv` is a *shared invariant*, a global fact that must hold after *every* atomic step taken
by *any* thread that knows about it. Because a shared invariant can never be violated, it's
freely duplicable. Any number of threads holding a reference to `c` can `unfold`/`fold` the
shared invariant `inv(c)`, on their own schedule, without ever "running out" the way they would
with a consumable resource. This is how an `inv` differs from a `pred` like Part 3's `valid`. A
`pred` is a resource that you fold and unfold as *part of your own accounting* and hand around
explicitly. An `inv` is a background truth that is shared by construction.

There's exactly one rule attached to this sharing: **a shared invariant instance may be open
(unfolded) for at most one atomic step before it must be folded again, and only one thread,
doing one thing, can have a given instance open at a time.** This is not a matter of style. It's
the condition that makes the whole approach sound, because between any two of *your* steps,
some other thread could have taken one of its own. Raven checks this rule purely syntactically,
before any SMT solving even starts:

- [`broken/two_atomic_steps.rav`](./broken/two_atomic_steps.rav) takes a read and then a write
  while `evenCount` is still open, and gets `[Verification Error] Attempting to take more than
  one atomic step with an open invariant or atomic update`.
- [`broken/forgotten_fold.rav`](./broken/forgotten_fold.rav) unfolds and never folds back, and
  gets `[Verification Error] Missing fold for unfolded invariant evenCount(c)`. The error is
  reported at the procedure's closing brace, where the omission is finally detected, with the
  `unfold` that opened the instance named as a Related Location.

**Masks, in a nutshell.** How does Raven know, at any given point in a proof, which invariants
can legally be opened? It tracks a *mask*, the set of invariant instances available to unfold at
that specific point. You never write a mask by hand in anything this tutorial covers. Raven
infers a callable's mask automatically from the invariants its `requires` clause mentions,
together with the invariants mentioned inside those invariants' own definitions. The mask
catches two concrete mistakes, both purely structural (no solver call is needed to catch either):

- **Re-entrant unfolding.** Unfolding the same instance twice without folding in between gets
  `[Verification Error] Invariant evenCount is already open`. This can be a literal
  `unfold evenCount(c); unfold evenCount(c);` typo or, more realistically, a call to a helper
  procedure that *also* unfolds `evenCount` while you still have it open.
- **Calling into a mask that isn't there.** If `bumpTwice` (`requires evenCount(c)`) is called
  while the caller already has `evenCount(c)` unfolded, `bumpTwice` can't get the folded resource
  its own precondition is asking for: `[Verification Error] Cannot call bumpTwice. The invariant
  evenCount required by bumpTwice is not available in the current mask.`

Both have the same kind of fix. Fold back what you have open *before* the call (or the second
unfold) that's causing trouble, and re-open it afterward if you still need it. With that in mind,
the `client` in [`hit_counter_invariant.rav`](./hit_counter_invariant.rav) spawns two
`bumpTwice`s and still proves `count % 2 == 0` afterward, without knowing how the two threads
interleaved with each other or with its own read. The invariant is what makes that uncertainty
irrelevant to the proof.

**Declaring what a callable opens.** The inferred mask covers every invariant reachable from
`requires`, whether or not the body ever opens it, and callers must have room for all of it.
When that is too much, a procedure or lemma can say what it opens with an `opens` clause, which
replaces the inferred mask: `opens {}` for nothing, `opens evenCount(c)` for one instance, or
`opens inner(x, _)` for every instance whose first argument is `x`. Raven checks the body
against the clause, and callers only need room for what it lists.

## Ghost fields and resource algebras {#sec:ghost-fields-resource-algebras}

Sometimes an invariant alone isn't enough. The `bump` procedure in `hit_counter_ghost.rav` uses
a CAS-retry loop (the standard way to do a "read, compute, write-if-nobody-else-changed-it"
update), and at one point needs to assert that the value hasn't gone backward between two reads:

```raven
assert v1 <= v2
```

Without help, this doesn't hold.
[`broken/no_ghost_state.rav`](./broken/no_ghost_state.rav) is this exact procedure with the ghost
bookkeeping stripped out, and its `assert` fails with `[Verification Error] This assertion may be
violated`. The invariant alone records *that* `count` holds some value at each step, but nothing
about its *history*. As far as the invariant is concerned, nothing rules out some other thread
having decreased it in between.

The fix is a **ghost field**. `ghost field seen: AuthMaxNat` holds a value from a *resource
algebra* (here, `Library.Auth[Library.MaxNat]`) rather than a program value, and exists purely
for the proof. It has no run-time representation at all. A resource algebra is more than a type.
It comes with its own notion of *composition*, which is what `&&` between two `own` facts on
the same field actually means, and that composition is specific to the kind of ghost value the
field stores. For `Auth[MaxNat]`, composing an authoritative piece `own(c.seen, auth_rag(v,
v))` with a fragment `own(c.seen, frag(w))` doesn't behave like ordinary conjunction at all. It's
closer to "the fragment `frag(w)` is a promise that the authoritative value `v` is *at least*
`w`," a lower bound that composition can only ever make tighter, never looser. Pairing the
real `count` field with a `seen` ghost field that is kept in sync with it is what lets the proof
hold onto that kind of promise, a piece of *stable knowledge about history*, even though `count`
itself, as a plain field, remembers nothing beyond its current value.
{{ref sec:frame-preserving-updates}} makes this precise.

Raven ships a small library of these constructions under `Library`:

- `Frac`, fractional permissions, which you've been using since Part 2 (every concrete field is
  implicitly wrapped in this one),
- `Excl`, a token that exactly one thread can hold,
- `Agree`, values that must agree to combine,
- `Auth`, an authoritative view plus distributable fragments,
- monotone counters like `MaxNat`.

You can also define your own. Part 5.1 does exactly that, and {{ref app:resource-algebras}} gives the formal
definition that every such algebra has to satisfy.

## Frame-preserving updates {#sec:frame-preserving-updates}

```raven
fpu(c.seen, auth(v1), auth(next))
```

The ghost statement `fpu` (frame-preserving update) replaces a ghost field's value according to
its resource algebra's own update relation. Here, that is `MaxNat`'s relation, which allows the
move from `v1` to `next` if `v1 <= next` and rejects the update in all other cases. The name is
worth unpacking, because it explains why this mechanism exists rather than a plain assignment to
the ghost field location. Recall from {{ref sec:ghost-fields-resource-algebras}} that a fragment
`frag(v1)` composed with the authoritative piece encodes "the true value is at least `v1`." That
relationship is the *frame*: whatever a concurrent holder of some disjoint fragment is relying
on. If `fpu` allowed the authoritative piece to move down to something smaller than a fragment
already handed out, the composition that the fragment's owner relies on would become invalid,
and the frame would not be *preserved*. `MaxNat`'s update relation is defined precisely to rule
that out. So `fpu`'s check, "is this move allowed by the algebra's own rules?", is what turns
"the counter never goes backward" from a hope into something Raven verifies once, statically, for
`bump` as a whole, rather than something that has to be trusted at run time. The
`assert v1 <= v2` a few lines earlier follows from that same check having gone through, and
doesn't need to be verified separately.

## Ghost blocks and the erasure guarantee {#sec:ghost-blocks-erasure}

Ghost code exists to support the proof. **Erasing it must preserve the program's non-ghost
state and control flow.** Raven's type checker enforces this boundary for `ghost` declarations,
proof statements, and **ghost blocks**, written `{! ... !}`. A ghost block marks its entire
statement sequence as ghost, as in [`ghost_scope.rav`](./ghost_scope.rav):

```raven
proc demo(c: Ref, implicit ghost v: Int)
  requires own(c.count, v)
  ensures own(c.count, v + 1)
{
  ghost var predictedNext: Int := v + 1
  bump(c)

  {!
    if (predictedNext > 0) {
      assert predictedNext == v + 1
    }
  !}
}
```

The `if` reads ghost state, so it must itself be ghost. Removing the block, as in
[`broken/ghost_leak.rav`](./broken/ghost_leak.rav), gives `This expression reads ghost state,
so it can only be used inside a ghost block, spec, or ghost-typed field`.

Ghost code can read and update ghost state, but it cannot assign to non-ghost variables or
fields. [`broken/ghost_write.rav`](./broken/ghost_write.rav) tries `c.count := 5` inside a ghost
block and gets `Cannot assign to non-ghost field count in ghost context`. It also cannot call
an ordinary `proc` or `spawn` a thread, just as a `lemma` cannot
({{ref sec:lemmas-and-axioms}}).

**Ghost statements do not count as atomic steps.** While a shared invariant is open, the
one-atomic-step rule from {{ref sec:shared-invariants}} counts only non-ghost steps. Ghost
assignments, assertions, `fpu`s, and lemma calls can surround that step. In
[`ghost_steps.rav`](./ghost_steps.rav), there is still only one real atomic operation:

```raven
proc bumpTwice(c: Ref)
  requires evenCount(c)
{
  unfold evenCount(c)
  ghost var predicted: Int := 2
  assert predicted == 2
  val _x := faa(c.count, 2) // the one real atomic step
  ghost var checked: Bool := true
  assert checked
  fold evenCount(c)
}
```

**Termination still has to be justified.** Raven assumes termination of a recursive `func` or
`lemma` unless you supply a `decreases` clause; the ghost-state checks do not establish it.
Give ghost recursion a checked termination measure. {{ref sec:ghost-termination}} shows why
this matters and what happens when the assumption is unfounded.

## Why this matters going forward

The toolkit from this chapter (shared invariants, masks, ghost fields, resource algebras, `fpu`,
ghost blocks) is the core of what makes Raven different from a purely sequential verifier. Part 5
doesn't introduce new logical machinery on top of it. Its first capstone (5.1, fork/join) applies
exactly this toolkit to a complete data structure without adding anything. It even includes a
`{! ... !}` block of its own, for a branch whose condition depends on ghost state just like the
one in {{ref sec:ghost-blocks-erasure}}. The two chapters after that introduce two conveniences
(atomic contracts and iterated separating conjunctions) that make the same toolkit scale to
bigger, more realistic concurrent data structures.

## Debugging Corner

This chapter has introduced four different kinds of failures. It's worth keeping them apart,
because they call for different fixes:

1. **Atomicity-analysis rejections** such as `Attempting to take more than one atomic step...`
   and `Missing fold for unfolded invariant %s` are syntactic. They name the exact discipline
   you broke and are flagged instantly (no solver call is involved at all). The fix is always to
   restructure the control flow: add the missing `fold`, or avoid taking two atomic steps while
   the invariant is open.
2. **Mask errors** such as `Invariant %s is already open` and `... is not available in the
   current mask` are also syntactic, and are also fixed structurally (see
   {{ref sec:shared-invariants}}). Fold back what's open before the unfold or call that's
   failing.
3. **A verifier-checked failure at an `fpu`** (`This update may not be frame-preserving`, or, as
   in {{ref sec:ghost-fields-resource-algebras}}–{{ref sec:frame-preserving-updates}}, a
   downstream `assert` that depends on ghost state you haven't set up yet) is not structural. The
   fix is to go back to the resource algebra's definition and check that the update you're
   asking for is one it allows.
4. **Ghost/non-ghost boundary errors** ({{ref sec:ghost-blocks-erasure}}) such as `This
   expression reads ghost state...`, `Cannot assign to non-ghost var/field ... in ghost
   context`, and `Cannot call procedure in ghost context` are type errors, caught before
   verification even starts. The fix is structural too. Either wrap the offending statement in a
   `{! ... !}` block (if what it reads is meant to be ghost), or stop trying to read/write/call
   the non-ghost side from ghost code (if it isn't).

## Exercise

[`exercises/min_max_tracker.rav`](./exercises/min_max_tracker.rav): a concurrent high-score/
low-score tracker. `reportHigh` (a running maximum) is done for you, following the recipe from
`hit_counter_ghost.rav` exactly. `reportLow` (a running *minimum*) is filled in except for one
line, the `fpu` that keeps its ghost field in sync, which is left for you to write.
The hint in the file explains the trick (tracking `-low` instead of `low`, since `MaxNat` only
moves up). A checked solution is in
[`solutions/min_max_tracker.rav`](./solutions/min_max_tracker.rav).

## What's next

[Part 5](../advanced/) doesn't ask you to learn new reasoning. Instead, it applies everything
from Parts 1–4 to four full case studies:

- fork/join (5.1), which needs no new mechanism at all and is built up starting from a first
  attempt that doesn't work,
- a ticket lock (5.2), using *atomic contracts*, a more convenient way to state what you've
  already been proving with invariants,
- an array of lockable counters (5.3), using *iterated separating conjunctions* to own an
  unboundedly large family of resources at once,
- a distributed counter (5.4), using *prophecy variables* and a "helping protocol" to handle a
  linearization point that depends on the future.
