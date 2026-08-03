# 5a. Capstone: Fork/Join

*Assumes: Parts 1–4, in full. Unlike 5b/5c, this capstone doesn't lean on any single new
mechanism — it's Parts 1–4's own toolkit (ownership, shared invariants, ghost fields and resource
algebras, the module system), applied once, start to finish, on a data structure you haven't seen
yet. If any of that still feels shaky, this is worth doing before 5b/5c, not after.*

Fork/join protects a different shape of synchronization than anything in Part 4: not "many
threads repeatedly touch shared state safely" (the counter), but "one thread computes a result of
some task exactly once, and another thread collects that result exactly once". Rather than
presenting the finished proof, this capstone builds it the way you'd actually arrive at it —
including a first, reasonable-looking attempt that doesn't work, and a detailed explanation
exactly why it doesn't.

## 1. The shape of the problem

```raven
interface Instance {
  type R
  pred resource(r: R)
  proc task() returns (r: R)
    ensures resource(r)
}

module ForkJoin[I: Instance] {
  proc fork() returns (p: Ref)
    ensures /* p is a fresh handle on the data structure */

  proc join(p: Ref) returns (r: R)
    requires /* p is a handle produced by fork */
    ensures resource(r)
}
```

The interface `Instance` abstracts over whatever `task` computes and whatever resource it hands
back. Procedure `fork()` is meant to start a worker thread running `task` in the background and
return immediately with a handle `p`; Procedure `join(p)` is meant to wait for that worker to
finish and hand back its `resource`.

## 2. A plan for transferring ownership

The implementation of `ForkJoin` declares `field value: Option[R]` so that the worker thread can
send the result value of the task to the *joining* thread. The field is initialized to
`Option.none` and the worker thread updates it to `Option.some(r)` to signal that the result `r`
of `task()` is ready.

The real question is how `resource(r)` — produced by the worker thread, deep inside `fork`'s
call to `spawn` — ends up back in the joining thread's hands. The natural answer is a shared
invariant, tracking whether the worker has posted its result yet:

```raven
inv is_forkjoin(p: Ref) {
  exists o: Option[R], b: Bool ::
    own(p.value, o) &&
    (o == Option.none ? true : (b ? true : resource(o.Option.value)))
}
```

The value `o` is `none` until the worker posts; `b` is meant to distinguish "posted, but not yet
claimed" (`b == true`, the invariant just sits on the resource) from "already claimed" (`b ==
false`, the invariant holds nothing, on the assumption that whoever claimed it took it for
good). Procedure `worker` posts by setting `o` and folding with `b := false`. Conversely, `join` reads `o`,
and if it's not `none`, means to fold with `b := true` and walk away with
`resource(o.Option.value)`. This is [`broken/no_token.rav`](./broken/no_token.rav); read it end
to end once, since it's the version of this data structure one may write first.

## 3. Why it fails

It doesn't verify. `join`'s `else` branch — the one that's supposed to return the claimed
resource — fails with `[Verification Error] A postcondition may not hold at this return point`,
related to `ensures resource(r)`. The invariant, as written, has no way to distinguish "I am the
thread that gets to claim `resource(r)`" from "some other thread already claimed it, or is about to."
Nothing stops two different threads from both reading `o != Option.none`, both folding the
invariant back with `b := true`, and both believing they're entitled to `resource(o.Option.value)`
— even though only one of them can actually have it. (Simplifying the invariant's `b ? true :
resource(...)` down to just `resource(...)` doesn't fix this either: the only way to actually
take the resource back out of the invariant for good would be to set `p.value` back to
`Option.none` at the same time — but that's a real change to `join`'s *implementation*, adding a
write with a genuine (if small) runtime cost, to fix what is really only a proof problem. The
implementation is already correct as it stands, provided `p` never leaks to a second thread that
could call `join` again — which is exactly the intended use here.) The invariant needs to encode
*exclusivity*, not just presence.

## 4. The idea: a token

What's missing is a way to prove "I am the only thread that could possibly be here". Suppose
there were a predicate `token(p)` — a non-duplicable permission slip — and a fact about it:

```raven
lemma token_unique(p: Ref)
  requires token(p) && token(p)
  ensures false
```

That is, no state can ever satisfy holding more than one `token(p)` at once. Then we can give
`fork`'s caller the one and only `token(p)` that will ever exist for this `p`, alongside
`is_forkjoin(p)`, and put a *second* copy inside the invariant itself whenever `b == true`
(posted, unclaimed):

```raven
inv is_forkjoin(p: Ref) {
  exists o: Option[R], b: Bool ::
    own(p.value, o) &&
    (o == Option.none ? true : (b ? token(p) : resource(o.Option.value)))
}

proc fork() returns (p: Ref)
  ensures is_forkjon(p) && token(p)

proc join(p: Ref) returns (r: R)
  requires  is_forkjon(p) && token(p)
  ensures resource(r)
```

Now the proof in `join` goes through, *assuming* `token_unique` is actually true. Right after
`unfold is_forkjoin(p)[b0 := b]`, if `o != Option.none` and `b0` turns out to be true, we obtain
one `token(p)` from the invariant on top of the one already held from `join`'s own `requires`,
never spent. That's `token(p) && token(p)`, so `token_unique` yields `false`, and `false` proves
anything, including the postcondition this scenario would otherwise be unable to
establish. Symbolically: `o.value != none && b0` combined with `token_unique` gives `o.value !=
none ==> !b0` — exactly the fact needed to know the `else` branch really does have
`resource(r)` sitting in the invariant, not another thread's token.

This idea is a complete, checkable file on its own, without committing to *how* `token` and
`token_unique` are realized yet: [`fork_join_abstract_token.rav`](./fork_join_abstract_token.rav).
It turns `ForkJoin` into an `interface` rather than a `module` for exactly this reason — a bare,
bodyless `pred` or `lemma` (`token`, `token_unique`) is only legal inside an interface, exactly
like `Counter`'s `valid` back in Part 3, never at the top level of a module.

## 5. Making the token real

`token_unique` isn't a law of nature; it has to come from *some* resource algebra whose
composition rule makes two `token`s contradictory. This is also the general mechanism worth
naming here: any proof can define its own proof-specific resource algebra to use as a ghost
field's type, simply by implementing the `Library.ResourceAlgebra` interface — Appendix A gives
the full formal picture, once you want it. `Excl` provides exactly what is needed in this proof:
a token that can never be duplicated, because composing two non-`id` elements always produces the
invalid `top`:

```raven
module Excl : Library.ResourceAlgebra {
  rep type T = data { case bot; case excl; case top }
  val id: T = bot
  func valid(a: T) returns (res: Bool) { a != top }
  func comp(a: T, b: T) returns (res: T) { a == id ? b : (b == id ? a : top) }
  func frame(a: T, b: T) returns (res: T) { b == id ? a : (a == excl && b == excl ? id : top) }
  func fpuAllowed(a: T, b: T) returns (res: Bool) { false }
}
```

Every `ResourceAlgebra` axiom (Appendix A) is either immediate from this `case` split, or, for
`fpuAllowed` — always `false` here — vacuously satisfied, since an algebra that never allows an
update trivially satisfies whatever soundness condition that update would have needed. With
`ghost field ex: Excl` and `pred token(p: Ref) { own(p.ex, Excl.excl) }`, `token_unique` gets a
real proof instead of an assumption:

```raven
lemma token_unique(p: Ref)
  requires token(p) && token(p)
  ensures false
{
  unfold token(p)
  unfold token(p)
}
```

Unfolding twice exposes two copies of `own(p.ex, Excl.excl)` — invalid by `Excl.comp`'s own
definition, which is what lets the empty rest of this body conclude `false`. This is
[`fork_join_explicit.rav`](./fork_join_explicit.rav): a complete, working proof, with `token` a
plain predicate — meaning every place that touches it needs an explicit `fold`/`unfold`.

## 6. More automation with `auto` predicates

Look at what step 5's version actually has to do, purely as bookkeeping, because `token` is
opaque. Procedure `fork` needs an explicit `fold token(p);` before it can even claim `ensures
token(p)`, since nothing about `own(p.ex, Excl.excl)` is visible through `token` without one. And
`join` needs an explicit call to `token_unique`, right where §4 said the proof needs it — after
unfolding `is_forkjoin(p)`, when `o` isn't `none` and `b0` turns out to be true:

```raven
{!
  if (o != Option.none && b0) {
    token_unique(p)
  }
!}
```

(sitting inside a `{! ... !}` ghost block, since its condition depends on a ghost variable, and
an ordinary `if` in a `proc` can't branch on ghost state — the same `{! !}` syntax you'll see
again in Appendix A if you go looking for more resource-algebra examples.) Every one of these
steps is mechanical, driven entirely by `Excl`'s own composition rule, never by any actual
case-by-case reasoning on your part. This is exactly the kind of bookkeeping `auto` predicates exist to
eliminate. Mark `token` `auto`:

```raven
auto pred token(p: Ref) {
  own(p.ex, Excl.excl)
}
```

and `token(p)` becomes, as far as any proof is concerned, simply another way of writing
`own(p.ex, Excl.excl)` — no `fold`/`unfold` ever needed to move between them. This has three
consequences, all visible in [`fork_join.rav`](./fork_join.rav), the final version:
`token_unique`'s proof shrinks to an empty body (`token(p) && token(p)` already expands to two
copies of the same `Excl` ownership, contradictory on its own), `fork`'s explicit `fold
token(p);` disappears, and the explicit call to `token_unique` inside `join` disappears too —
Raven now performs that exact reasoning automatically, every time `token(p)` appears, with
nobody asking it to. Compare `fork_join_explicit.rav` and `fork_join.rav` side by side once; the
difference is the entire ergonomic payoff of `auto pred`, in one worked example.

## Why this matters for concurrency

`interface Instance` and `module ForkJoin[I: Instance]` are the same functor pattern from Part 3
— a module abstracting over a client-supplied resource and a client-supplied *operation*
producing it (not just a resource, the way Part 3's `Counter` did). `ClientInstance`, `module FJ
= ForkJoin[ClientInstance]`, and `client()` at the bottom of `fork_join.rav` show the whole thing
instantiated and used, the same way `UsePlain = UseCounter[PlainCounter]` did back in Part 3.

## What's next

[5b](../atomic-contracts/) revisits this same existentials-plus-boolean-flag invariant shape for
repeated mutual exclusion instead of a one-shot handoff, and introduces atomic contracts as a
more ergonomic way to state what an invariant-based proof already proves by hand.
