# Appendix E: Standard Library Data Types

*Assumes: {{ref sec:algebraic-data-types}} (data types and `match`) and Part 3 (functors).*

Besides the built-in types from {{ref sec:values-and-types}}, the standard library provides
generic data types as functors in the module `Library`. This appendix describes the ones the
main tutorial doesn't use: options, lists, and sequences.

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
