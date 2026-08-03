# Appendix A: Resource Algebras, Formally

Part 4 introduced `Library.Frac`, `Library.Auth`, and `Library.MaxNat` by what problem each
solves. This appendix gives the formal definition underneath them, for readers who want the
constructions justified rather than motivated, and walks through defining a custom one.

## The definition

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

## The interface a custom RA implements

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

## Worked examples: `Excl` and `DisjSet`

Part 5a's [`fork_join.rav`](../05-advanced/fork-join/fork_join.rav) already had you read one
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
ticket is not anyone else's." To define your own algebra, you supply `T`, `id`, `valid`, `comp`,
`frame`, and `fpuAllowed`; Raven then checks the `ResourceAlgebra` axioms automatically, by
discharging them as ordinary proof obligations against your definitions — neither `Excl` nor
`DisjSet` needs an explicit proof of any of them, because they all follow directly from the
bodies given.

The standard library also has `Library.CancellativeResourceAlgebra` and
`Library.LatticeResourceAlgebra`, refinements that add cancellativity or a lattice structure and
unlock additional automation for algebras that satisfy them — `MaxNat` (Part 4) is a
`LatticeResourceAlgebra`; `DisjSet` above is `CancellativeResourceAlgebra`.
