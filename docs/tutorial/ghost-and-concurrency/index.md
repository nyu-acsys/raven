# 4. Ghost Code and Basic Concurrency

This is the part where Raven stops looking like a sequential program verifier and starts doing
what it's actually for. Everything from Parts 1–3 — ownership, fractional permissions, the frame
rule, modules — was building toward this: reasoning about a heap that more than one thread can
touch at once. There are two main companion files —
[`hit_counter_invariant.rav`](./hit_counter_invariant.rav) ({{ref sec:threads-and-atomics}}–{{ref sec:shared-invariants}}, no ghost state yet) and
[`hit_counter_ghost.rav`](./hit_counter_ghost.rav) ({{ref sec:ghost-fields-resource-algebras}}–{{ref sec:frame-preserving-updates}}, where ghost fields and resource
algebras enter) — plus a couple of small standalone ones for {{ref sec:ghost-blocks-erasure}}, on the ghost/non-ghost boundary
itself: [`ghost_scope.rav`](./ghost_scope.rav) and [`ghost_steps.rav`](./ghost_steps.rav).

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
`p` to terminate. The statement `faa` (fetch-and-add) is one of Raven's primitive *atomic* heap
operations. The `faa` statement in the example is equivalent to `c.count := c.count + 2` but
the read-and-increment of `c.count` happens as a single indivisible step. A data race, in
Raven, isn't something a separate tool has to hunt for after the fact: it's a proof that fails
to go through, for a reason that's about to become concrete.

## The problem shared invariants solve {#sec:shared-invariants-problem}

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

## Shared invariants {#sec:shared-invariants}

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
  gets `[Verification Error] Missing fold for unfolded invariant evenCount(c)`, reported at the
  procedure's closing brace — where the omission is finally detected — with the `unfold` that
  opened the instance named as a Related Location.

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

## Ghost fields and resource algebras {#sec:ghost-fields-resource-algebras}

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
`count` itself, as a plain field, remembers nothing beyond its current value. {{ref sec:frame-preserving-updates}} makes this
precise.

Raven ships a small library of these constructions under `Library` — `Frac` (fractional
permissions, which you've actually been using since Part 2: every concrete field is secretly
wrapped in this one), `Excl` (a token exactly one thread can hold), `Agree` (values that must
agree to combine), `Auth` (an authoritative view plus distributable fragments), and monotone
counters like `MaxNat`. You can also define your own — Part 5.1 does exactly that, and Appendix A
gives the formal definition every such algebra has to satisfy.

## Frame-preserving updates {#sec:frame-preserving-updates}

```raven
fpu(c.seen, auth(v1), auth(next))
```

The ghost statement `fpu` (frame-preserving update) replaces a ghost field's value according to
its resource algebra's own update relation — here, `MaxNat`'s, which is defined to allow the
move from `v1` to `next` if `v1 <= next` and rejects update in all other cases. The name is
worth unpacking, because it's the whole reason this mechanism exists rather than using a plain
assignment to update a ghost field location: recall from {{ref sec:ghost-fields-resource-algebras}} that a fragment `frag(v1)` composed
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

## Ghost blocks and the erasure guarantee {#sec:ghost-blocks-erasure}

Every `ghost` you've written since Part 2 — `implicit ghost v: Int`, `ghost field seen:
AuthMaxNat`, `ghost var v2: Int` in {{ref sec:ghost-fields-resource-algebras}} above — exists purely to help the proof along. None of it
is compiled: a real build of a Raven program erases every ghost declaration, every ghost-only
statement, and every `fold`/`unfold`/`fpu`, and the result runs identically. That's not a vague
slogan about intent; it's a precise guarantee, and a type-checking discipline exists specifically
to make it good: **erasing ghost code can never change what the non-ghost program actually
does** — not its non-ghost state, not which branches it takes, not whether or when it calls
another procedure.

`{! ... !}` — a **ghost block** — is the last piece of ghost syntax this tutorial introduces: it
wraps a whole sequence of statements and marks all of them ghost at once, the same way `ghost
var`/`ghost field` mark one declaration at a time. This is
[`ghost_scope.rav`](./ghost_scope.rav):

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

`ghost var predictedNext` is an ordinary local, declared exactly like `var`, that Raven erases
along with everything computed from it. The `if` right after it has to sit inside `{! ... !}`
precisely because its condition, `predictedNext > 0`, reads ghost state: an *ordinary* (non-ghost)
`if` can't branch on that, on pain of letting the real program's control flow depend on a fact
only the proof can see — [`broken/ghost_leak.rav`](./broken/ghost_leak.rav) is exactly this `if`
with the `{! ... !}` deleted, and it fails immediately with `[Type Error] This expression reads
ghost state, so it can only be used inside a ghost block, spec, or ghost-typed field`. Wrapping
the whole statement in a ghost block is what makes the condition legal: inside `{! ... !}`,
everything — the branch, the `assert` — is ghost too, so there's nothing left for the erasure
guarantee to protect.

The rule cuts the other way just as sharply: a ghost block can read and manipulate ghost state
freely, but it still can't reach out and touch anything real.
[`broken/ghost_write.rav`](./broken/ghost_write.rav) tries `c.count := 5` — an ordinary,
non-ghost field — from inside a `{! ... !}` block, and gets `[Type Error] Cannot assign to
non-ghost field count in ghost context`; the identical check guards a non-ghost local variable
one level down, `Cannot assign to non-ghost var x in ghost context`. And exactly like {{ref sec:lemmas-and-axioms}}'s
`lemma`, which can never call an ordinary `proc` (`[Type Error] Cannot call procedure in ghost
context`), the same restriction applies to any `proc` call — or `spawn` — written inside a ghost
block: nothing ghost is ever allowed to trigger a real side effect, including starting a new
thread. Between these checks — no reading ghost data into non-ghost expressions or control flow,
no writing non-ghost state from ghost code, no calling non-ghost callables from ghost code — the
type system closes every direction erasing ghost code could otherwise change real behavior.

This same distinction is exactly what {{ref sec:shared-invariants}}'s one-atomic-step rule leans on, and it's worth stating
outright: **ghost statements never count as one of the atomic steps that rule restricts.** A
shared invariant instance may be open for at most one atomic step — but that step has to be a
*real*, non-ghost one. Any number of ghost statements — a `ghost var` assignment, an `assert`, an
`fpu`, a `lemma` call, an entire `{! ... !}` block — can appear before it, after it, or both, without ever
tripping `Attempting to take more than one atomic step with an open invariant or atomic update`.
[`ghost_steps.rav`](./ghost_steps.rav) is {{ref sec:shared-invariants}}'s own `bumpTwice`, with a run of ghost bookkeeping
added on both sides of its one real `faa`:

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

This isn't a special case bolted onto the atomicity analysis. It's the erasure guarantee from
earlier in this section, seen from the concurrency side. A real execution of the compiled program
only ever takes the one non-ghost step; every ghost statement in between is gone once ghost code
is erased, so no additional real time passes, and there's no additional real step for another
thread to interleave with. Restricting an open invariant to at most one *non-ghost* step is
precisely capturing what another thread could actually observe; charging it for ghost bookkeeping
that no other thread can ever see would be counting something that, from any other thread's
point of view, never happened.

This is, in fact, the deeper reason Raven draws the ghost/non-ghost line as a static, type-checked
distinction in the first place, rather than a documentation convention: the atomicity analysis's
entire job is counting real steps, and it can only do that if it can tell, syntactically and
without a single solver call, which statements are real and which are proof bookkeeping that
vanishes before compilation. Every check earlier in this section — no reading ghost data into
non-ghost control flow, no writing non-ghost state from ghost code, no calling non-ghost
callables from ghost code — exists in service of that same fact: once the type checker has drawn
the ghost/non-ghost line once and for all, `unfold`/`fold`'s one-atomic-step rule (and everything
Part 5 builds on top of it) gets to trust that line completely, rather than re-deriving it itself.

Every direction, that is, except one: **termination**. [`ghost_termination_gap.rav`](./ghost_termination_gap.rav)
verifies — and that's the point, not a bug in the example:

```raven
lemma loopForever(n: Int)
  ensures false
{
  loopForever(n)
}

proc demo()
{
  {!
    loopForever(0)
  !}
  assert false
}
```

`loopForever` recurses on itself unconditionally, with no `decreases` clause — exactly the
situation {{ref sec:control-flow}} and {{ref sec:lemmas-and-axioms}} already flagged for `func`/`lemma`: without one, Raven doesn't
check termination, it silently *assumes* it. Nothing here fails any check from earlier in this
section — the call sits inside a `{! ... !}` block, nothing non-ghost is touched — so this
compiles all the way through to `assert false` succeeding, purely from an unfounded assumption
about ghost recursion. Add `decreases n` to `loopForever` and Raven immediately rejects it
instead: `[Verification Error] This decreases clause's termination measure may not decrease on
this recursive call`, because `n` never actually gets smaller across the call. That's the one
place this chapter's "erasure changes nothing" story is a discipline you have to uphold yourself,
not something the type checker enforces for you: give any ghost recursion you write a real
`decreases` clause, the same as you would for ordinary code.

## Why this matters going forward

This chapter's toolkit — shared invariants, masks, ghost fields, resource algebras, `fpu`, ghost
blocks — *is* the core of what makes Raven different from a purely sequential verifier. Part 5
doesn't introduce new logical machinery on top of any of it; its first capstone (5.1, fork/join)
puts exactly this toolkit to work on a complete data structure with nothing added (including a
`{! ... !}` block of its own, for a branch whose condition depends on ghost state exactly the way
{{ref sec:ghost-blocks-erasure}}'s does), and the two after that introduce two conveniences (atomic contracts, iterated
separating conjunctions) that make this same toolkit scale to bigger, more realistic concurrent
data structures.

## Debugging Corner

There are four genuinely different failure modes from this chapter that are worth keeping
distinct because they call for different fixes:

1. **Atomicity-analysis rejections** — `Attempting to take more than one atomic step...`,
   `Missing fold for unfolded invariant %s` — are syntactic. They name the exact discipline you broke,
   they're flagged instantly (no solver call involved at all), and the fix is always
   restructuring control flow: add the missing `fold`, don't take two atomic steps before the
   next one.
2. **Mask errors** — `Invariant %s is already open`, `... is not available in the current
   mask` — are also syntactic, and also fixed structurally (see {{ref sec:shared-invariants}}): fold back what's open
   before the unfold or call that's failing.
3. **A verifier-checked failure at an `fpu`** (`This update may not be frame-preserving`, or, as
   in {{ref sec:ghost-fields-resource-algebras}}–{{ref sec:frame-preserving-updates}}, a downstream `assert` that depended on ghost state you haven't set up yet) isn't
   structural — the fix is going back to the resource algebra's definition and checking the
   update you're asking for is actually one it allows.
4. **Ghost/non-ghost boundary errors** ({{ref sec:ghost-blocks-erasure}}) — `This expression reads ghost state...`, `Cannot
   assign to non-ghost var/field ... in ghost context`, `Cannot call procedure in ghost context`
   — are type errors, caught before verification even starts. The fix is always structural too:
   either wrap the offending statement in a `{! ... !}` block (if what it reads is genuinely
   meant to be ghost), or stop trying to read/write/call the non-ghost side from ghost code
   entirely (if it isn't).

## Exercise

[`exercises/min_max_tracker.rav`](./exercises/min_max_tracker.rav): a concurrent high-score/
low-score tracker. `reportHigh` (a running maximum) is done for you, following
`hit_counter_ghost.rav`'s recipe exactly. `reportLow` (a running *minimum*) is filled in except
for one line — the `fpu` that keeps its ghost field in sync — which is where you come in.
The hint in the file explains the trick (tracking `-low` instead of `low`, since `MaxNat` only
moves up); a checked solution is in [`solutions/min_max_tracker.rav`](./solutions/min_max_tracker.rav).

## What's next

[Part 5](../advanced/) doesn't ask you to learn new reasoning — it puts everything from
Parts 1–4 to work on four full case studies: fork/join (5.1, no new mechanism at all, built up
from a first attempt that doesn't work), a ticket lock (5.2, using *atomic contracts*, a more
ergonomic way to state what you've already been proving with invariants), an array of
lockable counters (5.3, using *iterated separating conjunctions* to own an unboundedly large
family of resources at once), and a distributed counter (5.4, using *prophecy variables* and a
"helping protocol" to handle a linearization point that depends on the future).
