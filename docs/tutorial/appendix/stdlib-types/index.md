# Standard Library Data Types

*Assumes: {{ref sec:algebraic-data-types}} (data types and `match`) and Part 3 (functors).*

Besides the built-in types from {{ref sec:values-and-types}}, the standard library provides
generic data types as functors in the module `Library`. This appendix describes the ones the
main tutorial doesn't use: options, lists, sequences, and arrays.

## Getting an instance {#sec:stdlib-instances}

Each data type is a functor over `Library.Type`, the interface of all types, so you choose the
element type by instantiating it. You can declare an instance explicitly, as in
`module IntList = Library.List[Library.IntType]`, where `Library.IntType`, `Library.BoolType` and
`Library.RefType` stand for the built-in types `Int`, `Bool` and `Ref`. You can also write the
instance as a type, as in `Library.List[Int]`, or let Raven infer it from a call
({{ref sec:implicit-functor-instantiation}}). Each instance's type is called `T`, and
`Library.Type` also gives every element type an unspecified value `default`.

## Options {#sec:stdlib-option}

`Library.Option[E]` holds either no value or one value of type `E`:

```raven
rep type T = data {
  case none
  case some(value: E)
}
```

`is_some(x)` tests for the second case. The examples in this appendix's first file,
[`options_and_lists.rav`](./options_and_lists.rav), include a function returning the first
element of a list, if there is one:

```raven
func first(l: IntList.T) returns (r: IntOption.T) {
  l == nil ? IntOption.none : IntOption.some(l.hd)
}
```

To get at the value, write `first(l).IntOption.value`. A destructor is a member of its module
like any other, so it needs the module's name unless the module is imported, as `IntList` is for
`l.hd` here.

## Lists {#sec:stdlib-list}

`Library.List[E]` is the familiar inductive list, built from `nil` and the infix constructor `::`
(with destructors `hd` and `tl`), together with two recursive functions: `len(l)`, the length of
`l`, and `is_in(l, e)`, whether `e` occurs in `l`. After `import IntList._`, you can write
lists as in `1 :: 2 :: nil` and use the functions unqualified. Lists are ordinary data types, so
you can define your own functions on them by recursion and `match`:

```raven
func sum(l: IntList.T) returns (r: Int)
  decreases l
{
  match l {
    case nil => 0
    case hd :: tl => hd + sum(tl)
  }
}
```

Raven unfolds the definitions of such functions automatically, so facts about concrete lists,
such as `sum(1 :: 2 :: nil) == 3`, hold without further proof.

## Sequences {#sec:stdlib-seq}

`Library.Seq[E]` provides immutable sequences with the following operations:

| Operation | Meaning |
|---|---|
| `empty`, `singleton(e)` | the empty sequence, and the sequence holding just `e` |
| `length(s)` | the number of entries of `s` |
| `index(s, i)` | the entry at position `i`, counting from 0 |
| `append(s, t)` | `s` followed by `t` |
| `update(s, i, e)` | `s` with the entry at position `i` replaced by `e` |
| `take(s, n)`, `drop(s, n)` | the first `n` entries of `s`, and the remaining ones |
| `contains(s, e)` | whether `e` is an entry of `s` |
| `equal(s, t)` | whether `s` and `t` are equal |

`index` is unspecified outside the range from 0 to `length(s) - 1`.

Unlike `List`, `Seq` is sealed ({{ref sec:sealing}}). Its interface, `Library.SeqSpec[E]`, states
the properties of these operations as `auto` lemmas, and those lemmas are all you see as a
client. `Seq` implements sequences as lists and proves the lemmas, but none of that is visible
outside it.

[`hit_log.rav`](./hit_log.rav) brings back the hit counter. This version keeps a log of its hits,
each numbered when it happens, instead of a number:

```raven
module HitLog {
  module Log = Library.Seq[Library.IntType]

  field log: Log.T

  pred valid(c: Ref, v: Int) {
    exists l: Log.T :: own(c.log, l) && Log.length(l) == v &&
      (forall i: Int :: {Log.index(l, i)} 0 <= i && i < v ==> Log.index(l, i) == i)
  }

  proc increment(c: Ref, ghost v: Int)
    requires valid(c, v)
    ensures valid(c, v + 1)
  {
    unfold valid(c, v)
    var l := c.log
    c.log := Log.append(l, Log.singleton(Log.length(l)))
    fold valid(c, v + 1)
  }

  // ... create and get
}
```

`valid(c, v)` says that the log of a counter with value `v` holds `0, 1, ..., v - 1`. The proof
of `increment` needs the length and the entries of the extended log, and `SeqSpec`'s lemmas about
`append`, `singleton`, `length` and `index` provide them without any help. The log itself appears
as an existentially quantified `l` in `valid`, and Raven finds it when you fold `valid`
({{ref sec:witness-computation}}).

One thing works differently from what you might expect. Two sequences with the same length and
the same entries are equal, but Raven doesn't compare sequences entry by entry on its own. Unless
`SeqSpec`'s lemmas rewrite one of them into the other, it concludes that they are equal only when
you ask whether they are `equal`. The lemma `split` at the end of `hit_log.rav` shows this:

```raven
import Library._

lemma split(s: Seq[Int], n: Int)
  requires 0 <= n && n <= Seq.length(s)
  ensures Seq.append(Seq.take(s, n), Seq.drop(s, n)) == s
{
  assert Seq.equal(Seq.append(Seq.take(s, n), Seq.drop(s, n)), s);
}
```

Here, `Seq[Int]` names the sequences of integers, and each call such as `Seq.length(s)` infers
the instance from the type of its argument ({{ref sec:implicit-functor-instantiation}}).

Without the `assert`, the postcondition fails. The assertion makes Raven compare the two
sequences entry by entry, and once it holds, the two are known to be equal.

## Arrays {#sec:stdlib-array}

Options, lists, and sequences are values. `Library.Array[E]` is different: an array is a family
of heap cells, one per index, each holding an entry of type `E` in its field `value`:

| Member | Meaning |
|---|---|
| `length(a)` | the number of cells of `a` |
| `loc(a, i)` | the cell at index `i`, a `Ref` |
| `arr(a, m)` | a predicate owning all cells of `a`, whose entries are given by the map `m` |
| `alloc(n, d)` | a procedure creating an array of `n` cells, each holding `d` |

`m` is `E.default` outside the bounds of `a`, so the entries determine it. Distinct indices, and
distinct arrays, have distinct cells. This is what lets an iterated separating conjunction like
the one in `arr` own all of them at once ({{ref sec:addressing}}). A `Ref` can't be
constructed in Raven, so this fact can't be proved. Like `alloc`, it is an axiom of the standard
library, which you can rely on instead of stating it yourself.

You access entries by indexing, as with maps. `x := a[i]` reads the entry at index `i`,
`a[i] := v` writes it, and `own(a[i], v)` owns it. These are short for `x := loc(a, i).value`,
`loc(a, i).value := v`, and `own(loc(a, i).value, v)`. Unlike a map lookup, though, `a[i]` is not
an expression. Like a field, an entry can only be read by an assignment, as in `x := a[i]` or
`var x := a[i]`, or named as a location in `own`. A trigger therefore mentions the cell, as in
`{loc(a, j)}` below.

[`arrays.rav`](./arrays.rav) sets all entries of an array to the same value:

```raven
proc fill(a: IntArray.T, x: Int, implicit ghost m: Map[Int, Int])
  requires arr(a, m)
  ensures arr(a, {| i: Int :: 0 <= i && i < length(a) ? x : m[i] |})
{
  unfold arr(a, m);
  var i := 0;
  while (i < length(a))
    invariant 0 <= i && i <= length(a)
    invariant forall j: Int :: {loc(a, j)} 0 <= j && j < i ==> own(a[j], x)
    invariant forall j: Int :: {loc(a, j)} i <= j && j < length(a) ==> own(a[j], m[j])
  {
    a[i] := x;
    i := i + 1;
  }
  fold arr(a, {| i: Int :: 0 <= i && i < length(a) ? x : m[i] |});
}
```

Inside the loop, `arr` is unfolded, so the invariants own the cells individually: those already
written hold `x`, the others still hold their entries from `m`. After the loop, folding `arr`
again packs them up into a single predicate with the new entries.

