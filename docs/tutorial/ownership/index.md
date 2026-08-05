# 2. Ownership and Resources

*No ghost state yet* — that's Part 4. This part is entirely about what it means to own a piece
of mutable heap state in the first place, and why "owning" a heap cell has to be a resource
you can run out of, not just a boolean fact you can freely assert. All code below is in
[`hit_counter_heap.rav`](./hit_counter_heap.rav), one file, verified together.

## Fields and the heap {#sec:fields-and-heap}

```raven
field count: Int

proc create() returns (c: Ref)
  ensures own(c.count, 0)
{
  c := new (count: 0)
}
```

The declaration `field count: Int` states that heap objects can have a `count` field. `Ref` is
Raven's type for heap references — but note that it's *opaque*: you cannot read or write through
a `Ref` just because you're holding one. The statement `new (count: 0)` allocates a fresh object
with its `count` field initialized to `0`. Moreover, in the very same step, hands the caller
ownership of exactly that field back as the *resource* `own(c.count, 0)` — nothing else. If your
program declares other fields besides `count`, this particular object still comes with no usable
access to them: only the fields you actually mention in a `new` statement's initializer come
with ownership attached, whether or not other fields exist elsewhere in the program. Try
deleting the `ensures` clause above and re-verifying `increment` below — it'll fail immediately,
because without it, `create`'s caller has a `Ref` but no permission to do anything with it.

One practical gotcha you'll hit immediately if you write heap-touching code by hand: **a single
statement can only perform one heap access.** `c1.count := c2.count;` doesn't type-check — read
`c2.count` into a local variable first, then write it. This isn't an arbitrary restriction: it's
a direct consequence of the same soundness discipline Part 4's shared invariants rely on. Every
basic statement is only allowed to take one step that's observable to other threads; reading
`c2.count` and writing `c1.count` is two such steps, and if they were combined into one
statement, another thread could interleave between them — writing to `c2.count` after it's been
read but before that value lands in `c1.count`, silently invalidating whatever the write thought
it was copying. (Part 2's exercises give you a first-hand look at the syntax; Part 4 is where
the concurrency reasoning behind the restriction becomes concrete.) In particular, this means
that you cannot use a field read like `c2.count` nested within a larger expression or statement.

## `own` is a resource, not a fact {#sec:own-resource-not-fact}

```raven
proc increment(c: Ref, implicit ghost v: Int)
  requires own(c.count, v)
  ensures own(c.count, v + 1)
{
  var x := c.count
  c.count := x + 1
}
```

The formal parameter `v` is declared as `implicit ghost`. Here `ghost` means that the parameter
exists purely to state the contract — it has no run-time effect. The modifier `implicit` means
that the caller does not need to supply an actual argument to `v` explicitly; Raven infers it
from whatever `own(c.count, ...)` fact is already in scope at the call site. The important idea
here is that `own(c.count, v)` is not merely the claim "`c.count` currently equals `v`" (that
would just be a fact, freely duplicable, like `2 + 2 == 4`). It's *ownership* of that fact:
something you can spend, and once spent, no longer have. Try this, in a scratch file:

```raven
proc badDup(c: Ref, implicit ghost v: Int)
  requires own(c.count, v)
  ensures own(c.count, v) && own(c.count, v)
{
}
```

This is [`broken/double_ownership.rav`](./broken/double_ownership.rav) — it's supposed to fail,
and it does, with `[Verification Error] A postcondition may not hold at this return point` and a
related location on the second `own(c.count, v)`. You cannot manufacture ownership out of
nothing just by writing it in an `ensures` clause. Raven checks that the resource you're
claiming to produce is actually backed by what you had. Internally, this is because `own` facts
about the same field compose via addition of their *permission fraction* — see {{ref sec:fractional-permissions}} — and two full
(100%) claims on the same cell add up to 200%, which is simply invalid.

## Separating conjunction {#sec:separating-conjunction}

The operator `&&` that we used inside the `ensures` clause of `badDuP` is not the boolean `&&`
you're used to — it's separation logic's *separating conjunction*. The assertion `own(c1.count,
v1) && own(c2.count, v2)` doesn't just claim both facts are true; it claims the *resources*
backing them can be split into two pieces that hold independently for each conjunct. This is
what licenses Raven's *frame rule*: whatever a procedure doesn't mention in its contract, it
provably cannot have touched or falsified. Consider the following procedure:

```raven
proc distinctIncrement(c1: Ref, c2: Ref, implicit ghost v1: Int, implicit ghost v2: Int)
  requires own(c1.count, v1) && own(c2.count, v2)
  ensures own(c1.count, v1 + 1) && own(c2.count, v2)
{
  assert c1 != c2; // provable from the requires clause alone, before this line
  var before := c2.count
  increment(c1)
  var after := c2.count
  assert before == after
}
```

The predicate `own(c2.count, v2)` is never mentioned again after the `requires` clause, yet it
reappears untouched in the `ensures` clause. That's not just true of the contract in the
abstract — the second `assert` makes it observable: `increment(c1)`'s own contract only ever
asks for (and hands back) `c1.count`, so `c2.count` is guaranteed unchanged across the call, and
reading it before and after really does give the same value. Nothing here tells Raven this
explicitly; it derives it automatically, because `c2`'s resource was never handed to `increment`
in the first place. This is the "frame problem" that plain Hoare logic struggles with: without a
*resource-aware* connective, you'd need to manually restate, for every call, everything the
callee definitely didn't change. Separating conjunction gets that for free.

## Fractional permissions {#sec:fractional-permissions}

```raven
proc readHalf(c: Ref, implicit ghost v: Int) returns (r: Int)
  requires own(c.count, v, 0.5)
  ensures own(c.count, v, 0.5) && r == v
{
  r := c.count
}

proc readTwice(c: Ref, implicit ghost v: Int) returns (a: Int, b: Int)
  requires own(c.count, v, 1.0)
  ensures own(c.count, v, 1.0) && a == v && b == v
{
  a := readHalf(c)
  b := readHalf(c)
}
```

The predicate `own(e.f, v, q)` takes an explicit third argument, a fraction `q` in `(0.0, 1.0]`;
omitting it (as every earlier example did) defaults to `1.0`, full ownership, which grants both
read and write access to `e.f`. Anything less than `1.0` — like `readHalf`'s `0.5` — grants
read-only access, since the remaining fraction might be held (and, by the same logic, might be
being read) by someone else. Procedure `readTwice` calls `readHalf` twice in a row from a single
full permission to `c.count`, splitting off `0.5` for each call — but not both at once. The
first `readHalf` call takes `0.5`, returns, and hands its `0.5` straight back to
`readTwice`. The returned fraction recombines with the `0.5` `readTwice` still held throughout
into the full `1.0` again; only then does the second call split off its own `0.5`. `readTwice`'s
own share of `c.count` never actually drops below `0.5`, at any point in its execution — and
that's the part worth pausing on, not just the splitting: because *something* is always held, no
other call (here, neither `readHalf` invocation, but the same reasoning covers any concurrent
thread accessing `c.count`) could have written to `c.count` in between, which is exactly what
lets Raven conclude both `readHalf` calls read back the same, still-unchanged `v` — `a == v && b
== v`. None of this is Raven-specific magic: it's just that `(v, 0.5)` composed with `(v, 0.5)`
equals `(v, 1.0)` in the fractional-permission algebra, and Raven's automatic framing is doing
ordinary algebra with that fact, the same way it matched up disjoint resources in {{ref sec:separating-conjunction}}.

## Procedure contracts, revisited {#sec:proc-contracts-revisited}

Put together, {{ref sec:own-resource-not-fact}}–{{ref sec:fractional-permissions}} mean a procedure contract genuinely describes a **resource transfer** at a
call, not just a logical fact. The `requires` clause is what the callee consumes from the
caller. The `ensures` clause is what it hands back. Anything the caller holds outside that exact
resource is guaranteed, by construction, to survive the call unchanged. This is different enough
from plain Hoare logic that it's worth restating directly: **you are not just proving properties
of values anymore, you are also accounting for who currently has permission to see and change
them.**

## Anti-aliasing, for free {#sec:anti-aliasing}

Look again at `distinctIncrement`'s `assert c1 != c2`. Nowhere did we write `requires c1 !=
c2`. It's *derivable*, automatically, from `own(c1.count, v1) && own(c2.count, v2)` alone: if
`c1` and `c2` were the same location, the caller would need to simultaneously hold two full
(100%) permissions on it, which — exactly as in {{ref sec:own-resource-not-fact}}'s `badDup` — is an inconsistent amount of
ownership to hold at once. So the only states satisfying the precondition in the first place are
ones where `c1 != c2` holds already. Compare this to a language without ownership tracking,
where "are these two references aliased?" has to be settled by a side-condition you write and
prove by hand, every time. Here, it falls out of the resource accounting you were doing anyway.

## Bundling resources with `pred` {#sec:bundling-pred}

Every contract so far has spelled out `own(c.count, v)` directly. That's fine for one field, but
it doesn't scale: real data structures need more than a single `own` fact to describe a
well-formed instance, and every operation's contract would otherwise have to repeat that whole
conjunction verbatim. Worse, nothing stops you from forgetting a conjunct in just one contract
and silently weakening what that operation's callers can rely on. A `pred` gives a name to a
fixed conjunction of resources and facts, so every contract can mention the name instead of
restating the pieces:

```raven
pred counter(c: Ref, v: Int) {
  own(c.count, v) && v >= 0
}
```

This declares a **predicate** `counter`, parameterized by a `Ref` and an `Int`, whose *body* is
exactly the kind of assertion you've already been writing in `requires`/`ensures` clauses. Unlike
`own`, though, a `pred` is **opaque by default**: once you have the resource `counter(c, v)`, you
cannot use `own(c.count, v)` or the fact `v >= 0` directly — as far as the verifier is concerned,
`counter(c, v)` is a single, indivisible resource, not a synonym for its body. Two operations
move between the two views:

```raven
proc make() returns (c: Ref)
  ensures counter(c, 0)
{
  c := new (count: 0)
  fold counter(c, 0)
}

proc bump(c: Ref, implicit ghost v: Int)
  requires counter(c, v)
  ensures counter(c, v + 1)
{
  unfold counter(c, v)
  var x := c.count
  c.count := x + 1
  fold counter(c, v + 1)
}
```

`fold counter(c, 0)` consumes whatever resources and facts the body describes — here,
`own(c.count, 0) && 0 >= 0`, both already established by the `new` statement just above it — and
produces the single opaque resource `counter(c, 0)` in exchange. `unfold counter(c, v)` is the
exact reverse: it consumes the opaque resource and hands back its body, so `bump` can go on to
read and write `c.count` directly. Both are ghost operations — like everything else that
manipulates resources rather than values, they compile away and have no run-time effect. Try
deleting `bump`'s `unfold` line and re-verifying: you'll get exactly `own is a resource, not a
fact`'s ({{ref sec:own-resource-not-fact}}) failure mode again, `[Verification Error] Could not assert sufficient permissions to
access this field` at `var x := c.count` — from the verifier's point of view, holding
`counter(c, v)` without unfolding it first is no different from not holding anything on
`c.count` at all.

Two things are worth noticing about what `fold` actually checks. First, it's not just
bookkeeping: `fold` re-derives the *entire* body, invariant included. Try changing `make`'s
`ensures counter(c, 0)` to `ensures counter(c, -1)`, its body to `c := new (count: -1)`, and its
`fold` to `fold counter(c, -1)` — you'll get `[Verification Error] Failed to fold predicate. The
body of the predicate may not hold at this point`, with a related location pointing at the
`v >= 0` conjunct itself, `This assertion may not hold.` The invariant is enforced *at every
fold*, not just assumed. Second, forgetting the closing `fold` entirely (leaving
`counter(c, v + 1)` unproduced at the end of `bump`) fails exactly like a missing `own` did in
{{ref sec:own-resource-not-fact}}'s `badDup`: `[Verification Error] A postcondition may not hold at this return point`, with a
related location `This predicate may not hold.` on the `ensures` clause. A `pred` is still a
resource in the {{ref sec:own-resource-not-fact}}–{{ref sec:separating-conjunction}} sense — it composes, it's consumed and produced by `fold`/`unfold`, and a
contract that promises one had better actually receive it.

The payoff is exactly what motivated this section: `bump`'s contract never mentions `v >= 0`
anywhere, yet every caller gets to rely on it. Unfold `counter(c, v)` at any point you hold it,
anywhere in the program, and the fact `v >= 0` comes back with it — for free, because it's baked
into what `fold` already checked on the way in. A hand-rolled contract carrying `v >= 0` as a
separate conjunct alongside `own(c.count, v)` would have to repeat that conjunct on *every*
operation to keep it truthfully in scope everywhere; miss it on just one, and the invariant
silently stops propagating from that point on. `counter` here is deliberately the same shape
you'll meet again as `valid` in [Part 3](../modules/) — that's not a coincidence: bundling
resources under a `pred` like this is the first half of what makes hiding a representation
behind an interface possible at all.

## Why this matters for concurrency

Fractional permissions are what will let two *threads* — not just two sequential callers — hold
compatible partial access to the same location at once in Part 4. `readHalf`/`readTwice`'s
"split now, recombine later" pattern is quietly rehearsing exactly the machinery that
shared-invariant reasoning needs; when Part 4 introduces a lock or a concurrent counter, the
resource-splitting story will look identical, just with "thread" written where "sequential
caller" is written here.

## Debugging Corner

Two shapes an ownership failure takes are worth telling apart:

- A **direct heap access** without enough permission (a bare `c.count` or `c.count := ...`
  where the ambient `own` fact's fraction, or its existence at all, doesn't cover it) surfaces
  as `[Verification Error] Could not assert sufficient permissions to access/assign this
  field`.
- A **procedure call** whose `requires` needs an `own` fact the caller doesn't currently have
  surfaces as a general `[Verification Error] A postcondition may not hold` or `A precondition
  may not hold for this call`, paired with a related-location `This own predicate may not hold`
  pinpointing the specific conjunct that's missing.

Neither message tells you *where* the missing permission went — Raven doesn't keep an ownership
history for you to consult. So the actual debugging technique, when this happens in a bigger
proof than the ones here, is **bisection**, in either of two forms. You can comment out the call
(or the body of the callee) you suspect is holding onto the resource longer than it should,
re-run "Raven: Verify File," and narrow down by which change makes the diagnostic move or
disappear — but that changes what the program actually does, which is sometimes not what you
want mid-investigation. The other form doesn't: insert a throwaway `assert own(c.count, ...)`
(with whatever value/fraction you expect to hold) at successive earlier points in the same
procedure, working backward from the failure, until you find the last point where the assertion
still succeeds — that's where the resource actually went missing. Since `assert` never changes
what the program does, this narrows down the same way without touching behavior at all.

## Exercises

Stubs in `exercises/`, checked solutions in `solutions/`.

1. **[`reset.rav`](./exercises/reset.rav)** — reset a counter to zero; fill in the body.
2. **[`swap.rav`](./exercises/swap.rav)** — swap two counters' values; fill in the body (watch
   out for the "one heap access per statement" rule from {{ref sec:fields-and-heap}}).

## What's next

[Part 3](../modules/) doesn't add any new reasoning principles — it's about *organizing* the
reasoning we already have. The counter grows an abstract interface, a second implementation, and
a functor, and {{ref sec:bundling-pred}}'s `pred counter` reappears as `valid`, this time declared *abstract* in an
interface so that not even its body — let alone the raw `own(c.count, ...)` underneath — is
visible to client code at all.
