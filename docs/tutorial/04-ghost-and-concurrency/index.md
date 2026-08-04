# 4. Ghost Code and Basic Concurrency

This is the part where Raven stops looking like a sequential program verifier and starts doing
what it's actually for. Everything from Parts 1–3 — ownership, fractional permissions, the frame
rule, modules — was building toward this: reasoning about a heap that more than one thread can
touch at once. There are two companion files:
[`hit_counter_invariant.rav`](./hit_counter_invariant.rav) (§§1–4, no ghost state yet) and
[`hit_counter_ghost.rav`](./hit_counter_ghost.rav) (§§5–6, where ghost fields and resource
algebras enter).

## 1–2. Threads and atomic primitives

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
`p` to terminate. The statement `faa` (fetch-and-add) is one of Raven's primitive *atomic* heap
operations. The `faa` statement in the example is equivalent to `c.count := c.count + 2` but
the read-and-increment of `c.count` happens as a single indivisible step. A data race, in
Raven, isn't something a separate tool has to hunt for after the fact: it's a proof that fails
to go through, for a reason that's about to become concrete.

## 3. The problem shared invariants solve

Try this — it's [`broken/no_invariant.rav`](./broken/no_invariant.rav):

```raven
proc client() returns (c: Ref)
{
  c := create()
  spawn increment(c) // Part 2's ownership-transfer `increment`
  spawn increment(c)
}
```

This fails immediately: `[Verification Error] A precondition may not hold for this call`, on the
*second* `spawn`. The first `spawn` already consumed the one full permission `create` produced;
there is nothing left to hand the second thread. This is the real gap, made concrete: Part 2's
resource-transfer model has no way to express "many threads share access to this cell, provided
each one's own step leaves it in a good state" — only "one owner has it, then hands it fully to
the next." That gap is exactly what a shared invariant fills.

## 4. Shared invariants

```raven
inv evenCount(c: Ref) {
  exists v: Int :: own(c.count, v) && v % 2 == 0
}
```

An `inv` is a *shared invariant*, a global fact that must hold after *every* atomic step, taken
by *any* thread that knows about it. Because a shared invariant can never be violated, it's
freely duplicable: any number of threads holding a reference to `c` can `unfold`/`fold` the
shared invariant `inv(c)`, on their own schedule, without ever "running out," the way a
consumable resource would. That's the difference from a `pred` like Part 3's `valid`: a `pred`
is a resource you fold and unfold as *part of your own accounting*, handed around explicitly;
an `inv` is ambient background truth, shared by construction.

There's exactly one rule attached to that sharing: **a shared invariant instance may be open
(unfolded) for at most one atomic step before it must be folded again — and only one thread,
doing one thing, can have a given instance open at a time.** This isn't a style preference —
it's the condition that makes the whole thing sound, because between any two of *your* steps,
some other thread could have taken one of its own. Raven checks this rule purely syntactically,
before any SMT solving even starts:

- [`broken/two_atomic_steps.rav`](./broken/two_atomic_steps.rav) takes a read and then a write
  while `evenCount` is still open, and gets `[Verification Error] Attempting to take more than
  one atomic step with an open invariant or atomic update`.
- [`broken/forgotten_fold.rav`](./broken/forgotten_fold.rav) unfolds and never folds back, and
  gets `[Error] Missing fold for unfolded invariant evenCount(c)`, reported at the procedure's
  closing brace — where the omission is finally detected — with the `unfold` that opened the
  instance named as a Related Location.

**Masks, in a nutshell.** How does Raven know, at any given point in a proof, which invariants
are even legal to open? It tracks a *mask*: the set of invariant instances available to unfold at
that specific point. You never write a mask by hand in anything this tutorial covers — Raven
infers a callable's mask automatically, from which invariants syntactically appear in its own
body and contract, together with whatever the callables it calls need in turn. What the mask
actually buys you is catching two very concrete mistakes, both purely structural (no solver call
needed to catch either):

- **Re-entrant unfolding.** Unfolding the same instance twice without folding in between —
  whether that's a literal `unfold evenCount(c); unfold evenCount(c);` typo, or (more
  realistically) calling a helper procedure that *also* unfolds `evenCount` while you still have
  it open — gets `[Verification Error] Invariant evenCount is already open`.
- **Calling into a mask that isn't there.** If `bumpTwice` (`requires evenCount(c)`) is called
  while the caller already has `evenCount(c)` unfolded, `bumpTwice` can't get the folded resource
  its own precondition is asking for: `[Verification Error] Cannot call bumpTwice. The invariant
  evenCount required by bumpTwice is not available in the current mask.`

Both fixes are the same shape: fold back what you have open *before* the call (or the second
unfold) that's causing trouble, and re-open it afterward if you still need it. With that in mind,
[`hit_counter_invariant.rav`](./hit_counter_invariant.rav)'s `client` spawns two `bumpTwice`s and
still proves `count % 2 == 0` afterward, with no idea how the two threads actually interleaved
with each other or with its own read — the invariant is what lets that uncertainty stay
irrelevant to the proof.

## 5. Ghost fields and resource algebras

Sometimes an invariant alone isn't enough. `hit_counter_ghost.rav`'s `bump` uses a CAS-retry loop
(the standard way to do a "read, compute, write-if-nobody-else-changed-it" update), and at one
point wants to assert that the value hasn't gone backward between two reads:

```raven
assert v1 <= v2
```

Without help, this doesn't hold — literally: [`broken/no_ghost_state.rav`](./broken/no_ghost_state.rav)
is this exact procedure with the ghost bookkeeping stripped out, and that `assert` fails with
`[Verification Error] This assertion may be violated`. The invariant alone remembers *that*
`count` holds some even... er, some value at each step, but nothing about its *history* — as far
as the invariant is concerned, nothing rules out some other thread having decreased it in
between.

The fix is a **ghost field**: `ghost field seen: AuthMaxNat` holds a value from a *resource
algebra* (here, `Library.Auth[Library.MaxNat]`) rather than a program value, and exists purely
for the proof — it has no run-time representation at all. A resource algebra isn't just a type;
it comes with its own notion of *composition*, which is what `&&` between two `own` facts on
the same field actually means, and that composition is specific to the kind of ghost value the
field stores. For `Auth[MaxNat]`, composing an authoritative piece `own(c.seen, auth_rag(v,
v))` with a fragment `own(c.seen, frag(w))` isn't like ordinary conjunction at all — it's
closer to "the fragment `frag(w)` is a promise that the authoritative value `v` is *at least*
`w`," a lower bound that composition can only ever make tighter, never looser.  Pairing the
real `count` field with a `seen` ghost field kept in lockstep is what gives the proof a way to
hold onto that kind of promise — a piece of *stable knowledge about history* — even though
`count` itself, as a plain field, remembers nothing beyond its current value. §6 makes this
precise.

Raven ships a small library of these constructions under `Library` — `Frac` (fractional
permissions, which you've actually been using since Part 2: every concrete field is secretly
wrapped in this one), `Excl` (a token exactly one thread can hold), `Agree` (values that must
agree to combine), `Auth` (an authoritative view plus distributable fragments), and monotone
counters like `MaxNat`. You can also define your own — Part 5a does exactly that, and Appendix A
gives the formal definition every such algebra has to satisfy.

## 6. Frame-preserving updates

```raven
fpu(c.seen, auth(v1), auth(next))
```

The ghost statement `fpu` (frame-preserving update) replaces a ghost field's value according to
its resource algebra's own update relation — here, `MaxNat`'s, which is defined to allow the
move from `v1` to `next` if `v1 <= next` and rejects update in all other cases. The name is
worth unpacking, because it's the whole reason this mechanism exists rather than using a plain
assignment to update a ghost field location: recall from §5 that a fragment `frag(v1)` composed
with the authoritative piece encodes "the true value is at least `v1`". That composed-with
relationship is the *frame* — literally, whatever a concurrent holder of some disjoint fragment
is relying on. If `fpu` allowed the authoritative piece to move down to something smaller than
a fragment already handed out, the composition that fragment's owner is relying on would become
invalid — the frame would not be *preserved*. `MaxNat`'s update relation is defined precisely
to rule that out, so `fpu`'s check — "is this move actually allowed by the algebra's own rules"
— is what turns "the counter never goes backward" from a hope into something Raven verifies
once, statically, for `bump` as a whole, rather than something anyone has to trust at run
time. The `assert v1 <= v2` a few lines earlier is a consequence of that same check having
already gone through, not a separate thing that actually needs to be verified.

## Why this matters going forward

This chapter's toolkit — shared invariants, masks, ghost fields, resource algebras, `fpu` —
*is* the core of what makes Raven different from a purely sequential verifier. Part 5 doesn't
introduce new logical machinery on top of any of it; its first capstone (5a, fork/join) puts
exactly this toolkit to work on a complete data structure with nothing added, and the two after
that introduce two conveniences (atomic contracts, iterated separating conjunctions) that make
this same toolkit scale to bigger, more realistic concurrent data structures.

## Debugging Corner

There are three genuinely different failure modes from this chapter that are worth keeping
distinct because they call for different fixes:

1. **Atomicity-analysis rejections** — `Attempting to take more than one atomic step...`,
   `Missing fold for unfolded invariant %s` — are syntactic. They name the exact discipline you broke,
   they're flagged instantly (no solver call involved at all), and the fix is always
   restructuring control flow: add the missing `fold`, don't take two atomic steps before the
   next one.
2. **Mask errors** — `Invariant %s is already open`, `... is not available in the current
   mask` — are also syntactic, and also fixed structurally (see §4): fold back what's open
   before the unfold or call that's failing.
3. **A verifier-checked failure at an `fpu`** (`This update may not be frame-preserving`, or, as
   in §5–6, a downstream `assert` that depended on ghost state you haven't set up yet) isn't
   structural — the fix is going back to the resource algebra's definition and checking the
   update you're asking for is actually one it allows.

## Exercise

[`exercises/min_max_tracker.rav`](./exercises/min_max_tracker.rav): a concurrent high-score/
low-score tracker. `reportHigh` (a running maximum) is done for you, following
`hit_counter_ghost.rav`'s recipe exactly. `reportLow` (a running *minimum*) is filled in except
for one line — the `fpu` that keeps its ghost field in sync — which is where you come in.
The hint in the file explains the trick (tracking `-low` instead of `low`, since `MaxNat` only
moves up); a checked solution is in [`solutions/min_max_tracker.rav`](./solutions/min_max_tracker.rav).

## What's next

[Part 5](../05-advanced/) doesn't ask you to learn new reasoning — it puts everything from
Parts 1–4 to work on three full case studies: fork/join (5a, no new mechanism at all, built up
from a first attempt that doesn't work), a ticket lock (5b, using *atomic contracts*, a more
ergonomic way to state what you've already been proving with invariants), and an array of
lockable counters (5c, using *iterated separating conjunctions* to own an unboundedly large
family of resources at once).
