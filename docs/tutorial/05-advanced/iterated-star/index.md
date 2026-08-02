# 5c. Iterated Separating Conjunctions — Capstone: A Shelf of Counters

*Assumes: Part 2's separating conjunction and frame rule (§§2.3, 2.5), and Part 4's shared
invariants (§4.4). Not re-taught here — skim [Part 2](../../02-ownership/) and
[Part 4](../../04-ghost-and-concurrency/) first if either feels shaky.*

Every invariant so far has protected a fixed, small number of fields: one counter, two fields on
a lock. What if you need to protect an *unbounded* family of them — an array of `n` independent
counters, say, where `n` is only known at run time? Declaring `n` separate invariants isn't an
option (you don't know `n` at the point you'd write the declaration, and even if you did, that's
`n` copies of the same boilerplate). This is what an **iterated separating conjunction** (ISC)
is for: a `forall` inside an assertion that isn't a boolean fact, but a whole *family* of `own`
facts, one per value of the bound variable, all owned together.

All code below is in [`shelf_of_counters.rav`](./shelf_of_counters.rav).

## The ISC

```raven
inv shelfInv(s: S) {
  exists counts: Map[Int, Int] ::
    forall i: Int :: {S.loc(s, i)} 0 <= i && i < S.size(s) ==> own(S.loc(s, i).count, counts[i], 1.0)
}
```

Read the `forall` as "for every valid index `i`, own the `count` field of the `i`-th cell,
currently holding `counts[i]`" — one `own` fact per `i`, all held simultaneously, and all folded
or unfolded together as a single unit. This one declaration covers a shelf of *any* size; nothing
here depends on how large `S.size(s)` turns out to be at run time.

## Addressing, and why it's abstract

`S.loc(s, i)` is an uninterpreted function from a shelf and an index to a `Ref` — there's no
literal array-of-heap-cells underneath, just an axiom:

```raven
auto lemma all_diff()
  ensures forall s: T, i: Int :: {loc(s, i)} first(loc(s, i)) == s && second(loc(s, i)) == i
```

`first`/`second` are left inverses of `loc`: given `loc(s, i)`, you can always recover the
`s`/`i` that produced it. That's what lets Raven conclude `loc(s, i) != loc(s, j)` whenever `i !=
j` — exactly the fact needed to make sense of "own `n` different cells at once" as anything
other than nonsense.

Two honest notes on why this tutorial reasons about addressing this way, rather than
concretely allocating `n` cells in a loop and using a real `Map[Int, Ref]`: first, it's exactly
what Raven's own array benchmarks do (`test/arrays/array_utils.rav`,
`test/iterated-star/array-max.rav` — real, tested code, not a simplification invented for this
tutorial). `test/arrays/array_utils.rav` itself is expected to eventually move onto
`Library.Array`, an axiomatization of exactly this addressing scheme that's on its way into
Raven's trusted base specifically to simplify array reasoning like this — worth watching for if
you're writing this kind of proof yourself. Second, proving injectivity for a family of
locations built up incrementally, one `new` at a time, turns out to be a meaningfully harder
proof than this capstone is about — not just harder, but a *different kind* of proof: Raven
checks an ISC's injectivity side condition once, as a property of the predicate's own
definition, for arbitrary arguments, which a specific runtime `Map[Int, Ref]` value can't
satisfy no matter what you know about it at a given call site. If you want to see this worked
out anyway, [`exercises/shelf_growth.rav`](./exercises/shelf_growth.rav) is a real, if
differently-shaped, stretch goal: a shelf built by prepending one cell at a time, the same way a
Treiber stack grows, which sidesteps the injectivity question entirely by not using an ISC for
the growing part at all.

## The injectivity side condition

This isn't decorative — try deleting `all_diff` and its axiom (kept as
[`broken/no_injectivity.rav`](./broken/no_injectivity.rav)) and stating the same `forall`
`own`: it fails immediately with `[Verification Error] Could not prove the injectivity of the
index expression for this iterated separating conjunction`. This is the ISC's one silent side
condition, checked as a genuine proof obligation every time: without it, two different values of
the bound variable could describe the *same* `own` fact twice over, which is the family-sized
version of Part 2's `badDup` — claiming to independently own a resource you actually only have
one copy of.

## Touching one slot, without disturbing the rest

```raven
proc bump(s: S, i: Int)
  requires shelfInv(s) && 0 <= i && i < S.size(s)
  ensures shelfInv(s)
{
  S.all_diff();
  var cell := S.loc(s, i);
  ghost var counts: Map[Int, Int];
  unfold shelfInv(s)[counts := counts];
  val _x := faa(cell.count, 1);
  fold shelfInv(s)[counts := counts[i := counts[i] + 1]];
}
```

There's no syntax for "just open slot `i`" — `unfold`/`fold` always act on the whole invariant.
But semantically, only `counts[i]` is ever read or changed here; every other slot's `own` fact
passes through the unfold/fold pair completely undisturbed. That's the frame rule from Part 2
again, at a larger scale: the same mechanism that let `distinctIncrement` leave `c2` untouched
now lets `bump` leave every slot except `i` untouched, out of a family whose size isn't even
fixed at verification time.

`ShelfClient.client` spawns two `bump`s at (potentially different) indices `i` and `j`
concurrently, then `peek`s one of them — safe regardless of which pair of indices gets picked,
or how large the shelf actually is, because `shelfInv` was declared exactly once.

## Debugging Corner

One new diagnostic this section introduces: `Could not prove the injectivity of the index
expression for this iterated separating conjunction`, whenever an ISC's bound-variable-to-
location mapping isn't provably one-to-one. Resist the urge to fix this by reaching for your own
axiom, the way `all_diff` looks like a template for — every axiom you add is one more thing
Raven trusts without proof, and an addressing scheme's injectivity is exactly the kind of fact
that's easy to state wrong in a way that's hard to notice (an axiom that's actually inconsistent
lets *anything* be proved, silently). If you need array-like addressing, reach for
`Library.Array` instead: it gives you injective addressing for free, already proven correct once
rather than assumed anew in every proof that needs it.

## Exercise

[`exercises/shelf_growth.rav`](./exercises/shelf_growth.rav): the "shelf grows by one cell"
stretch goal from earlier — a shelf built by prepending one cell at a time rather than addressed
via an ISC. `mkEmpty` is done for you; `grow` is missing one line, the `fold` that
re-establishes the shelf one cell longer. A checked solution is in
[`solutions/shelf_growth.rav`](./solutions/shelf_growth.rav), whose comments spell out the
trade-off this representation makes against the ISC's: growing costs nothing extra, but
reaching a specific cell to touch it costs an unfold/fold per link along the way there.

## What's next

[5d](../automation/) collects the smaller automation features — implicit parameters, witness
computation, `auto` lemmas, triggers, `assert ... with` — that this capstone and 5b's ticket
lock (and, in its own way, 5a's fork/join) have all been quietly leaning on without calling out
by name (the `{S.loc(s, i)}` triggers above, for instance).
