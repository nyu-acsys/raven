# Appendix A: Resource Algebras, Formally

Part 4 introduced `Library.Frac`, `Library.Auth`, and `Library.MaxNat` by what problem each
solves. This appendix gives the formal definition underneath them, for readers who want the
constructions justified rather than motivated, and walks through defining a custom one.

## The definition {#sec:ra-definition}

A resource algebra (RA) is a tuple `(M, valid, id, comp, frame, fpuAllowed)`, where `M` is a set
(the carrier), `valid: M -> Bool` picks out which elements can actually be owned, `id` is a unit
element, and `comp`, `frame: M x M -> M` and `fpuAllowed: M x M -> Bool` are operations/relations
satisfying:

- `valid(id)`
- `comp` is associative, commutative, and has `id` as its unit
- `valid(comp(a, b)) ==> valid(a) && valid(b)` — composing can't manufacture validity from
  invalid pieces
- `valid(a) ==> frame(a, id) == a`
- `valid(frame(a, b)) ==> comp(frame(a, b), b) == a` — `frame` computes something like a right
  inverse of `comp`
- `valid(comp(a, b)) ==> valid(frame(comp(a, b), b))`
- `fpuAllowed(a, b) && valid(comp(a, c)) ==> valid(comp(b, c))` — the soundness condition for
  frame-preserving updates: replacing an owned `a` with `b` can never invalidate what a
  concurrent owner of some disjoint `c` was relying on

`comp` is what `&&` (separating conjunction) means at the level of a single field:
`own(e.f, a) && own(e.f, b)` is equivalent to `own(e.f, comp(a, b))`. `frame` is what lets Raven
compute what remains of a field's value after part of it is given up — e.g. by calling a `proc`
that requires it in its precondition. `fpuAllowed` (written
`fpuAllowed` in the tool, matching `Library.ResourceAlgebra`'s member name) is the relation
`fpu` checks before letting an update on a ghost field through.

Every field in a Raven program, concrete or ghost, holds an element of some resource algebra.
An ordinary `field f: T` is fixed to `Library.Frac[T]`, the fractional-permission algebra Part 2
was already using under the hood: `own(e.f, v, q)` is sugar for ownership of the fraction-`q`
chunk of value `v` in that algebra. A `ghost field g: A` uses whatever algebra `A` you name
explicitly.

## The interface a custom RA implements {#sec:ra-interface}

```raven
interface ResourceAlgebra : Library.Type {
  rep type T
  val id: T
  func valid(a: T) returns (ret: Bool)
  func comp(a: T, b: T) returns (ret: T)
  func frame(a: T, b: T) returns (ret: T)
  func fpuAllowed(a: T, b: T) returns (ret: Bool)

  auto axiom idValid() ensures valid(id)
  auto axiom compCommute() ensures forall a: T, b: T :: comp(a, b) == comp(b, a)
  auto axiom compAssoc()
    ensures forall a: T, b: T, c: T :: comp(comp(a, b), c) == comp(a, comp(b, c))
  auto axiom compId() ensures forall a: T :: comp(a, id) == a
  auto axiom compValid()
    ensures forall a: T, b: T :: valid(comp(a, b)) ==> valid(a) && valid(b)
  auto axiom frameId() ensures forall a: T :: valid(a) ==> frame(a, id) == a
  auto axiom compFrameInv()
    ensures forall a: T, b: T :: valid(frame(a, b)) ==> comp(frame(a, b), b) == a
}
```

These axioms are marked `auto` in the library itself, so once a module implements
`ResourceAlgebra`, the SMT solver can rely on them wherever that algebra's operations appear,
without anything re-stating them.

## Worked examples: `Excl` and `DisjSet` {#sec:ra-worked-examples}

Part 5a's [`fork_join.rav`](../advanced/fork-join/fork_join.rav) already had you read one
of these end to end — its hand-rolled `Excl` (a non-duplicable token: any two non-`id` elements
compose to the invalid `top`) is about as simple as a resource algebra gets, and every axiom
above is either immediate from its `case` split or, for `fpuAllowed` (`false`, unconditionally),
vacuously satisfied. Worth a second look now that you've seen the general definition: every
piece of that module maps directly onto one of the six things this appendix's interface asks
for.

A second, slightly richer example — the one Raven's own ticket lock (Part 5b) actually uses, via
`Auth[DisjSet[Int]]`, to track which tickets have been issued:

```raven
module DisjSet[X: Type] : CancellativeResourceAlgebra {
  rep type T = data {
      case set(value: Set[X]); case top
  }

  val id: T = set({||})

  func valid(n: T) returns (ret: Bool) { n == set(n.value) }

  func comp(a: T, b: T) returns (ret: T) {
      a is set && b is set && a.value ** b.value == {||} ?
        set(a.value ++ b.value) : top
  }

  func frame(a: T, b: T) returns (ret: T) {
      a is set && b is set && b.value subseteq a.value ?
        set(a.value -- b.value) : top
  }

  func fpuAllowed(a: T, b: T) returns (ret: Bool) {
      false
  }
}
```

Here, `top` is the canonical invalid element (returned whenever an operation would otherwise be
nonsensical, like composing two sets that aren't actually disjoint), and `comp` requires
disjointness — exactly what makes `own(l.tickets, ...)` a meaningful way to say "this thread's
ticket is not anyone else's."

`fpuAllowed` returning `false` unconditionally is worth dwelling on, because it's not laziness —
`DisjSet` genuinely cannot allow `fpuAllowed(a, b)` to hold for a `b` containing an element not
already in `a`, and the general soundness axiom from "The definition" above says exactly why.
Recall it: `fpuAllowed(a, b) && valid(comp(a, c)) ==> valid(comp(b, c))`, for *every* `c` — `c`
standing for whatever some other, concurrent owner might hold, disjoint from your own `a`. The
trouble is that knowing `a` alone puts no bound whatsoever on what such a `c` could be; anything
disjoint from `a` is a legal choice. So if `b` contained some element `x` not already in `a`,
nothing rules out a concurrent `c` that happens to already contain that very `x` too — `c = {x}`
is disjoint from `a` (since `x ∉ a`) and so `valid(comp(a, c))` holds, but `comp(b, c)` is now
`top`, invalid, because `b` and `c` share `x`. That's precisely a violation of the axiom above:
replacing `a` with `b` would have invalidated something a concurrent owner of `c` was relying on
— namely, that it exclusively owned `x` as part of `c`. `DisjSet` alone has no way to rule this
out, because *nothing in a bare `own(l.tickets, DisjSet.set(...))` fact bounds what any other
thread might separately own* — so `fpuAllowed` can only ever safely say "no" to growing the
set. (Shrinking, by the same argument, would actually be safe — a subset of `a` is automatically
disjoint from any `c` that `a` was — but `DisjSet` doesn't bother offering it either, since
nothing in its one real use, the ticket lock discussed next, ever needs to take a ticket back.)

This is exactly what motivates pairing `DisjSet` with `Library.Auth` rather than using it bare.
`Auth`'s own `fpuAllowed` is different in kind: it lets the *authoritative* piece grow, precisely
when the newly added part is simultaneously claimed by your *own* fragment, and nothing about
what any other fragment-holder has is disturbed. That's soundness-preserving for a reason
`DisjSet` alone can never provide: `Auth`'s validity condition already forces *every* fragment
anyone legitimately holds to be contained in the current authoritative value — so the
authoritative value itself *is* a global upper bound on everything anyone else could possibly
own. Growing it to include a brand-new element `x` is therefore safe, because no other fragment
could already contain an `x` that wasn't even in the bound yet. This is exactly
`ticket_lock_invariant.rav`'s `acquire`: the one `fpu` on `l.tickets` grows the authoritative
ticket set from `{0..nxt}` to `{0..nxt+1}` and this thread's own fragment from `{}` to `{nxt}` in
the same step — the new ticket enters the global bound and this thread's claim on it at once,
which is exactly the shape `Auth`'s local-update rule is built to allow. The general lesson: if a
proof needs to safely *increase* a resource mid-proof, and doing so soundly depends on having a
global upper bound on what every other thread could concurrently own, `Library.Auth` is the tool
that gives you that bound — a bare resource algebra like `DisjSet`, with nothing else, cannot
supply it on its own.

To define your own algebra, you supply `T`, `id`, `valid`, `comp`, `frame`, and `fpuAllowed`;
Raven then checks the `ResourceAlgebra` axioms automatically, by discharging them as ordinary
proof obligations against your definitions — neither `Excl` nor `DisjSet` needs an explicit proof
of any of them, because they all follow directly from the bodies given.

The standard library also has `Library.CancellativeResourceAlgebra` and
`Library.LatticeResourceAlgebra`, refinements that add cancellativity or a lattice structure and
unlock additional automation for algebras that satisfy them — `MaxNat` (Part 4) is a
`LatticeResourceAlgebra`; `DisjSet` above is `CancellativeResourceAlgebra`.
