# Well-Founded Orders

*Assumes: {{ref sec:termination-measure}} and the interfaces and modules from Part 3.*

Raven provides termination orders for common measures. This appendix explains how those
orders are represented and how to define one for a new type.

## Ackermann's lexicographic measure {#sec:ackermann-termination}

{{ref sec:termination-measure}} introduced a pair of integer counters. Ackermann's function,
in [`termination.rav`](./termination.rav), uses the same ordering with nested recursion:

```raven
func ackermann(m: Int, n: Int) returns (r: Int)
  decreases m, n
{
  m <= 0 ?
    n + 1 :
    (n <= 0 ? ackermann(m - 1, 1) : ackermann(m - 1, ackermann(m, n - 1)))
}
```

The inner call, `ackermann(m, n - 1)`, keeps `m` unchanged and decreases `n`. The outer call,
`ackermann(m - 1, ...)`, decreases `m`, regardless of the inner call's result. That result can
make the second component larger, so decreasing `n` alone would not justify every call.

[`broken/ackermann_single_measure.rav`](./broken/ackermann_single_measure.rav) uses just
`decreases m`. Raven rejects it with `This decreases clause's termination measure may not
decrease on this recursive call`: the inner call leaves `m` unchanged. The pair `m, n`
accounts for both kinds of descent.

## Defining a custom order {#sec:well-founded-order}

{{ref sec:termination-measure}} used a lexicographic `decreases m, n`, built from `Int`'s
built-in order. Behind the scenes, every `decreases` clause is resolved the same way, by the
*type* of the expression you give it. That type needs an instance of
`Library.WellFoundedOrder`, an ordinary interface from the standard library:

```raven
interface WellFoundedOrder : Type {
  func lt(x: T, y: T) returns (res: Bool)
  func embed(x: T) returns (res: OrdinalBase.T)

  axiom lt_embed_mono()
    ensures forall x: T, y: T :: {lt(x, y)} lt(x, y) ==> OrdinalBase.lt(embed(x), embed(y))
}
```

This is the `axiom` pattern from {{ref sec:lemmas-and-axioms}} once again. Implementing
`WellFoundedOrder` means supplying `lt`, and then either discharging `lt_embed_mono` yourself
with a real `lemma` body, or letting Raven attempt it automatically (which fails if the fact
doesn't hold). The function `embed` is what makes well-foundedness checkable rather than merely
assumed. Every instance has to map its own `T` into `Library.OrdinalBase.T`, the ordinals in
Cantor normal form. This is the one well-founded structure that the whole mechanism ultimately
trusts. You then need to prove that `embed` is a homomorphism for `lt` with the ordinal order. A
pullback of a well-founded relation is always well-founded, so this reduces the
well-foundedness of *every* instance to a single trusted fact. You don't have to prove the
non-existence of an infinite descending chain directly each time, which, for most interesting
orders, is much harder to show from scratch.

Raven ships five instances of `WellFoundedOrder`:

- `Library.IntOrder`, which is what every plain-`Int` `decreases` clause you've written so far
  resolves to.
- `Library.LexOrder[A, B]`, the lexicographic combinator from {{ref sec:termination-measure}},
  generic over any two well-founded orders `A` and `B`.
- `Library.Ordinal`, the raw ordinals themselves.
- `Library.MultisetOrder`, for a termination argument of the form "some multiset only ever
  shrinks," which no fixed-arity lexicographic tuple can express.
- `Library.SetOrder[E]`, strict subset inclusion on `FinSet[E]` (see
  {{ref sec:values-and-types}}). It is resolved automatically in the same way, so `decreases s`
  just works for any `FinSet`-typed `s` without naming an instance explicitly.

See `lib/ext/decreasesExt/well_founded_order.rav` if you want the details on any of these.
There's also a sixth built-in option that you may already have used without noticing. If you
write `decreases` on a value of a self-recursive `data` type (a `List[E]`'s tail, a tree's
child), Raven automatically generates a structural "subterm" order: `x` counts as smaller
than `y` exactly when `x` is one of the pieces `y` was built from. This is what makes
straightforward structural recursion over your own recursive algebraic data types work without
any of the machinery in this section. If your own measure doesn't fit any of these, you implement
`WellFoundedOrder` yourself, just like any other interface.
[`well_founded_order.rav`](./well_founded_order.rav) is a minimal complete example: a two-state
"not done yet"/"done" order, collapsing towards `true`:

```raven
module BoolOrder : Library.WellFoundedOrder {
  rep type T = data {
    case wrap(unwrap: Bool)
  }

  func lt(x: T, y: T) returns (res: Bool) {
    x.unwrap && !y.unwrap
  }

  func embed(x: T) returns (res: Library.OrdinalBase.T) {
    x.unwrap ?
      Library.OrdinalBase.zero :
      Library.OrdinalBase.cons(Library.OrdinalBase.zero, 1, Library.OrdinalBase.zero)
  }

  lemma lt_embed_mono()
    ensures forall x: T, y: T :: {lt(x, y)} lt(x, y) ==> Library.OrdinalBase.lt(embed(x), embed(y))
  {
  }
}
```

One detail is easy to miss and can cost real debugging time. `rep type T` is defined as a
one-case wrapper around `Bool`, not as `rep type T = Bool` directly. A `rep type` alias to a type
from *outside* the module resolves transparently to that other type's own identity once
elaborated. So a bare alias here would make a `decreases` clause of this type quietly resolve to
plain `Bool` (which has no `WellFoundedOrder` instance at all) rather than to `BoolOrder`.
`Library.Ordinal`, in the standard library itself, wraps `Library.OrdinalBase.T` for the same
reason.

## Termination of ghost code {#sec:ghost-termination}

{{ref sec:ghost-blocks-erasure}} explains the type checks that prevent ghost code from changing
non-ghost state or control flow. Those checks do not establish termination. For recursive
`func`s and `lemma`s, Raven assumes termination unless a `decreases` clause asks it to check a
measure. An unfounded assumption can invalidate a proof, even when the ghost-state rules hold.

[`ghost_termination_gap.rav`](./ghost_termination_gap.rav) is a complete example that verifies
under this assumption:

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

The recursive call assumes `loopForever`'s postcondition, so its body can establish `false`.
Calling the lemma then lets `demo` establish `false` as well. No non-ghost state is touched;
the missing justification is that this recursive proof terminates.

Adding `decreases n` makes Raven check that justification. It rejects the recursive call with
`This decreases clause's termination measure may not decrease on this recursive call`, because
`n` is unchanged. Give every recursive `func` or `lemma` a checked measure, including those
used only in ghost code.
