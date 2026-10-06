# 5.3. Iterated Separating Conjunctions (Capstone: A Shelf of Counters)

*Assumes: Part 2's separating conjunction and frame rule ({{ref sec:separating-conjunction}},
{{ref sec:proc-contracts-revisited}}), and Part 4's shared invariants ({{ref sec:shared-invariants}}).
These are not re-taught here. Skim [Part 2](../../ownership/) and
[Part 4](../../ghost-and-concurrency/) first if either feels shaky.*

Every invariant so far has protected a small, fixed number of fields, such as one counter or two
fields of a lock. What if you need to protect an *unbounded* family of them, say an array of `n`
independent counters, where `n` is only known at run time? Declaring `n` separate invariants
isn't an option. You don't know `n` at the point where you'd write the declaration, and even if
you did, that would mean `n` copies of the same boilerplate. This is what an **iterated
separating conjunction** (ISC) is for. It is a `forall` inside an assertion that denotes not a
boolean fact, but a whole *family* of `own` facts, one per value of the bound variable, all owned
together.

All code below is in [`shelf_of_counters.rav`](./shelf_of_counters.rav).

## The ISC {#sec:the-isc}

```raven
inv shelfInv(s: Counts.T) {
  exists counts: Map[Int, Int] ::
    forall i: Int :: {loc(s, i)} 0 <= i && i < length(s) ==> own(loc(s, i).value, counts[i], 1.0)
}
```

Read the `forall` as "for every valid index `i`, own the `value` field of the `i`-th cell,
currently holding `counts[i]`." There is one `own` fact per `i`, all held simultaneously, and all
folded or unfolded together as a single unit. This one declaration covers a shelf of *any* size.
Nothing here depends on how large `length(s)` turns out to be at run time.

## Addressing {#sec:addressing}

The shelf is an array from the standard library, `Counts = Library.Array[Library.IntType]`
({{ref app:stdlib-types}} describes arrays in more detail). Its counters are the `value` fields
of the array's cells, `loc(s, i)` is the cell at index `i`, and `length(s)` is the number of
cells. `loc` isn't defined in terms of anything else, since there's no way to construct a `Ref`
in Raven. Instead, the library states an axiom:

```raven
free auto axiom all_diff()
  ensures forall a: T, i: Int :: {loc(a, i)} first(loc(a, i)) == a && second(loc(a, i)) == i
```

`first`/`second` are left inverses of `loc`: given `loc(s, i)`, you can always recover the
`s`/`i` that produced it. That's what lets Raven conclude `loc(s, i) != loc(s, j)` whenever `i !=
j`. This is exactly the fact needed for "own `n` different cells at once" to make sense. Like the
library's `alloc`, which creates an array, the axiom is part of Raven's trusted base, stated once
rather than anew in every proof that needs it.

Why not allocate `n` cells one at a time with `new` and keep them in a `Map[Int, Ref]` instead?
Proving injectivity for a family of locations built up incrementally is a considerably harder
proof than what this capstone is about. It is also a *different kind* of proof. Raven checks an
ISC's injectivity side condition once, as a property of the predicate's own definition, for
arbitrary arguments. A specific runtime `Map[Int, Ref]` value can't satisfy that, no matter what
you know about it at a given call site. If you want to see a shelf built up incrementally anyway,
[`exercises/shelf_growth.rav`](./exercises/shelf_growth.rav) is a stretch goal that takes a
different approach. It builds a shelf by prepending one cell at a time, the same way a Treiber
stack grows, and avoids the injectivity question entirely by not using an ISC for the growing
part at all.

## The injectivity side condition {#sec:injectivity-side-condition}

The axiom is essential. [`broken/no_injectivity.rav`](./broken/no_injectivity.rav) states the
same kind of ISC over an addressing function that has no such axiom. It fails immediately with `[Verification Error] Could not prove the injectivity of the
index expression for this iterated separating conjunction`. This is the ISC's one implicit side
condition, and it is checked as a real proof obligation every time. Without it, two different
values of the bound variable could describe the *same* `own` fact twice. That would be the
family-sized version of Part 2's `badDup`, claiming to independently own two copies of a resource
you actually only have one copy of.

## Touching one slot, without disturbing the rest {#sec:touching-one-slot}

```raven
proc bump(s: Counts.T, i: Int)
  requires shelfInv(s) && 0 <= i && i < length(s)
  ensures shelfInv(s)
{
  val cell := loc(s, i)
  ghost var counts: Map[Int, Int]
  unfold shelfInv(s)[counts := counts]
  val _x := faa(cell.value, 1)
  fold shelfInv(s)[counts := counts[i := counts[i] + 1]]
}
```

There's no syntax for "just open slot `i`", since `unfold`/`fold` always act on the whole
invariant. Semantically, however, only `counts[i]` is ever read or changed here. Every other
slot's `own` fact passes through the unfold/fold pair completely undisturbed. That's the frame
rule from Part 2 again, at a larger scale. The same mechanism that let `distinctIncrement` leave `c2` untouched
now lets `bump` leave every slot except `i` untouched, out of a family whose size isn't even
fixed at verification time.

`ShelfClient.client` spawns two `bump`s at (potentially different) indices `i` and `j`
concurrently, then `peek`s one of them. This is safe regardless of which pair of indices gets
picked or how large the shelf actually is, because `shelfInv` was declared exactly once.

## Debugging Corner

This section introduces one new diagnostic, `Could not prove the injectivity of the index
expression for this iterated separating conjunction`, which appears whenever an ISC's mapping
from bound variable to location isn't provably one-to-one. Resist the temptation to fix this by
writing your own axiom, using `all_diff` as a template. Every axiom you add is one more thing
Raven trusts without proof, and the injectivity of an addressing scheme is exactly the kind of
fact that's easy to state incorrectly in a way that's hard to notice (an inconsistent axiom
silently lets *anything* be proved). If you need array-like addressing, use `Library.Array`
instead. Its injective addressing is part of Raven's trusted base, stated once rather than anew
in every proof that needs it.

## Exercise

[`exercises/shelf_growth.rav`](./exercises/shelf_growth.rav): the "shelf grows by one cell"
stretch goal from earlier, a shelf built by prepending one cell at a time rather than addressed
via an ISC. `mkEmpty` is done for you. `grow` is missing one line, the `fold` that
re-establishes the shelf one cell longer. A checked solution is in
[`solutions/shelf_growth.rav`](./solutions/shelf_growth.rav), whose comments spell out the
trade-off this representation makes compared to the ISC. Growing costs nothing extra, but
reaching a specific cell costs an unfold/fold for each link along the way.

## What's next

[5.4](../prophecies/) is the next and last capstone. It covers a distributed counter whose `get`
operation doesn't always know its own linearization point without help from a concurrent `incr`.
The solution combines prophecy variables with a "helping protocol" built from everything up to
this point: one-shot handoffs from 5.1, atomic contracts from 5.2, and, in the counter's own
invariant, an ISC over a *set* rather than an index range. [5.5](../automation/) then collects
the smaller automation features (implicit parameters, witness computation, `auto` lemmas,
triggers, `assert ... with`) that all four capstones have been relying on without discussing them
explicitly, such as the `{loc(s, i)}` triggers above.
