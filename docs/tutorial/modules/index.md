# 3. The Module System

Nothing in this part adds a new *reasoning* principle — everything here is still ordinary
sequential ownership from Part 2. What's new is *organization*: hiding a representation behind
an interface, giving that interface more than one implementation, and composing implementations
with functors. All code below is in
[`counter_interface.rav`](./counter_interface.rav), verified together.

## Interfaces and modules {#sec:interfaces-and-modules}

```raven
interface Counter {
  rep type T
  pred valid(c: T, v: Int)

  proc create() returns (c: T)
    ensures valid(c, 0)
  // ... increment, get, an axiom -- see the full file
}
```

An `interface` is a named bundle of members, some of which are left *abstract*: `rep type T`
has no definition, `pred valid` has no body, the `proc`s have no implementation. `rep type`
marks `T` as the interface's *representation type* — the payoff is that anywhere a type is
expected, you can write the module's own name and Raven expands it to `Counter.T` for
you. That's why `Counter`'s procedures can write `c: T` and, once you get to `UseCounter[C:
Counter]` below, callers can write `c: C` within `UseCounter` rather than spelling out `c: C.T`
everywhere.

`pred valid(c: T, v: Int)` is {{ref sec:bundling-pred}}'s `pred counter` with the body removed. There,
`counter`'s body — `own(c.count, v) && v >= 0` — sat right there for anyone reading the
declaration to see, and `fold`/`unfold` against it were legal anywhere that body was in scope.
Here, `valid` is only a *signature*: a name and a parameter list, nothing else. An interface can
declare that a predicate exists and what it's parameterized over, but never what it actually
asserts — because "what it asserts" is exactly the representation-specific detail no client of
`Counter` should get to depend on. That absence has a direct consequence for `fold`/`unfold` in
particular: both need the body to check what they're consuming or producing, so neither one is
usable against `valid` from outside a module that has actually supplied that body. Only once a
`module M : Counter` gives `valid` a real definition ({{ref sec:implementing-interface}}, next) does folding or unfolding it
become possible at all — and only *inside* `M`, since nowhere else does the body come into
scope.

## Implementing an interface {#sec:implementing-interface}

```raven
module PlainCounter : Counter {
  rep type T = Ref
  field count: Int

  pred valid(c: T, v: Int) {
    own(c.count, v) && v >= 0
  }
  // ... create/increment/get, matching Counter's contracts exactly
}
```

`module M : I { ... }` is a promise: every abstract member of `I` gets a real definition in
`M`, and Raven checks that each one's contract genuinely matches what `I` declared. Here that
body is, verbatim, {{ref sec:bundling-pred}}'s `counter` predicate — `PlainCounter` is that same running example,
now supplying the body its interface withheld. From this point on, `PlainCounter`'s own
`create`/`increment`/`get` can `fold`/`unfold` `valid` exactly the way Part 2's `make`/`bump`
did; what's changed is that nothing *outside* `PlainCounter` can. What you get in return is real
information hiding — see {{ref sec:abstract-predicates}}.

## Abstract predicates as a specification boundary {#sec:abstract-predicates}

The whole point of leaving `valid` abstract in the interface is that a client never gets to look
past it. [`counter_interface.rav`](./counter_interface.rav) has *two* implementations:
`PlainCounter`, the direct Part 2 representation, and `OffsetCounter`, which stores `v + 1000`
in its one field instead of `v` directly. They share nothing at the representation level. But
`UseCounter[C: Counter]`'s `demo` procedure is written once, against `Counter` alone, and
verifies identically whether `C` is instantiated to `PlainCounter` or `OffsetCounter`. Go look
at the two `module UsePlain = ...` / `module UseOffset = ...` lines at the bottom of the file.
This is what "abstract predicate as a specification boundary" means concretely: `valid` is the
entire interface between a `Counter`'s clients and its internals, in both directions.

## Lemmas and axioms {#sec:lemmas-and-axioms}

A `lemma` is Raven's proof-only callable. Syntactically, it is almost a `proc` (same
parameters, same `requires`/`ensures`, a statement-based body), but with the two restrictions
that make it about proof rather than computation. First, like a `func`, it must actually
terminate, which Raven silently *assumes* by default rather than checks, unless you give it a
`decreases` clause (the same discipline, and the same good-practice advice, as
{{ref sec:control-flow}}). Second, and more fundamentally, a `lemma` can never affect the *running* program: it can
never call an ordinary `proc` or `spawn` a thread (`[Type Error] Cannot call procedure in ghost
context` is what happens if you try). The entire callable, body included, disappears before
compilation, exactly like every other ghost construct you've seen since Part 2.

That erasure is the key to what a `lemma` actually *is*: its body isn't really executed at all.
It's a proof, written in the shape of a program, that the verifier walks through step by step to
justify a logical fact — the lemma's own contract — the same way a mathematical proof's steps
justify a theorem. This is the "programs as proofs" idea in miniature: Raven checks a `lemma`'s
body using the exact same machinery it uses to check a `proc`'s, but nothing about the result is
ever compiled or run.

With `lemma` understood, **an axiom is a lemma with no body**. In other words, it is a proof
obligation you're stating but not (yet) discharging, an assumption rather than an established
fact. The two are interchangeable. The `axiom` keyword just makes the "this is an assumption"
reading explicit at the declaration site. When a module implements an interface that declares
an axiom, that axiom has to become an established fact for *this particular module*. You have
two options to do so. You can supply it as a `lemma` with the same name and contract, but now
with a real proof body. Alternatively, if you omit to provive an implementation for it, Raven
automatically attempts to discharge the axiom's exact statement on its own, ultimately handing
it to the SMT solver with no help from you:

```raven
axiom nonNegative(c: T, ghost v: Int)
  requires valid(c, v)
  ensures valid(c, v) && v >= 0
```

Try deleting the `lemma nonNegative { ... }` block from `PlainCounter` and re-verifying: Raven's
automatic attempt **fails**, even though "a counter's value is never negative" looks obvious. The
reason is worth elaborating on: `valid` is an opaque, foldable predicate as far as the verifier
is concerned. Nothing about what's *inside* it — here, the fact that its definition happens to
include `v >= 0` — is visible to a proof unless something explicitly `unfold`s it first. So every
implementation supplies its own proof, as a `lemma` with the exact same name and contract as the
axiom: `unfold valid(c, v); fold valid(c, v);` is enough here, since unfolding is exactly what
exposes the `v >= 0` conjunct, and folding immediately back hands the resource back to the
caller. That last step matters: an axiom about a resource should generally hand the resource
back in its `ensures` (notice `nonNegative`'s `ensures` includes `valid(c, v)`, not just
`v >= 0`) unless it's deliberately meant to consume it — the Sum exercise below is where you'll
feel *why*, if you skip this.

## Functors {#sec:functors}

```raven
module UseCounter[C: Counter] {
  import C.valid

  proc demo() {
    var c := C.create()
    C.increment(c, 0)
    var r := C.get(c, 1)
    assert r == 1
    assert valid(c, 1)
  }
}

module UsePlain = UseCounter[PlainCounter]
module UseOffset = UseCounter[OffsetCounter]
```

`UseCounter[C: Counter]` is a *functor*: a module parameterized by another module, here
constrained to satisfy `Counter`. `module UsePlain = UseCounter[PlainCounter]` instantiates it,
specializing procedure `demo` against `PlainCounter` specifically. This is the mechanism that
lets a proof be written once and reused against every implementation of an interface, rather
than copy-pasted per implementation — here, the `assert` statements in `demo` are that proof.

It's worth being precise about what's actually been proved by the time both instantiations
exist, because the module system isn't just abstracting over *proofs* here — it's abstracting
over a real *implementation*, parametric in another implementation. Tally it up: `UseCounter`
itself gets implemented, and proved correct, exactly *once*, against `Counter` alone. Separately,
`PlainCounter` and `OffsetCounter` each get implemented and proved correct exactly once, each
against `Counter`'s contracts, for *every* way either one might ever be used — not just this
particular `demo`. `UsePlain` and `UseOffset` then simply compose these already-finished proofs:
instantiating `UseCounter[PlainCounter]` doesn't ask Raven (or you) to discharge one further
proof obligation, because none is left — the functor's proof already covers any `Counter`, and
`PlainCounter` already comes with a proof that it is one.

## Implicit functor instantiation {#sec:implicit-functor-instantiation}

Every functor use so far has needed an explicit instantiation first — `module UsePlain =
UseCounter[PlainCounter]` — before anything could be called through it. For a functor whose
*every* formal is constrained by an interface that itself declares a `rep type` (exactly the
shape `Counter` has, and the shape any interface built the way {{ref sec:interfaces-and-modules}} describes will have), Raven can
skip that step and infer the instantiation for you, right at the call site. This code is
[`implicit_instantiation.rav`](./implicit_instantiation.rav), a self-contained example:

```raven
module Box[T: Library.Type] {
  rep type S = data {
    case box(unwrap: T)
  }

  func mk(a: T) returns (res: S) {
    box(a)
  }

  func get(b: S) returns (res: T) {
    b.unwrap
  }
}

proc demo() {
  var b := Box.mk(3)
  assert Box.get(b) == 3
}
```

`Box.mk(3)` never instantiates `Box` by name anywhere. `mk`'s formal is declared `a: T` — `T`
being `Box`'s own, still-abstract formal — and the actual argument `3` has type `Int`; unifying
the two solves `T := Int` and Raven silently instantiates `Box[Int]` on your behalf, under an
internal name you never see or write. `Box.get(b)` resolves the same way but from the other
direction: `get`'s parameter is typed `S`, `Box`'s own rep type, so instead of unifying against a
plain argument, Raven reads the type argument straight back off `b`'s already-inferred type. The
same mechanism covers destructor syntax too — `b.Box.unwrap` resolves identically, without you
ever having written down which instantiation of `Box` `b` belongs to.

Calling `Box.mk(3)` a second time resolves to the *same* implicit instantiation as the first —
Raven deduplicates by the inferred type argument, so both calls' results share one type and can
be compared with `==`. A call with a different inferred argument, like `Box.mk(true)`, gets its
own separate instantiation, coexisting with `Box[Int]` in the same proc.

Eligibility is checked structurally, not by name: it's specifically "every formal's constraining
interface has a `rep type`" that qualifies a functor, which is why `Library.Type` (`Box`'s own
constraint on `T`) and `Counter` both work — both declare one. `UseCounter` itself, from {{ref sec:functors}},
technically qualifies the same way, since `Counter` has a `rep type` — but `demo` takes no
arguments at all, so there's nothing in a call to `UseCounter.demo()` for Raven to infer `C` from,
and you're back to writing `UseCounter[PlainCounter]` explicitly. If a formal's constraining
interface has no `rep type` in the first place, the functor doesn't qualify at all, and a bare
`F.member` fails with the ordinary "unknown identifier" error, exactly as if `F` were never
declared to have a member `member` — because, without an instantiation, it doesn't.

Inference can fail even for an eligible functor, when nothing about a call actually pins down a
formal. [`broken/box_underdetermined.rav`](./broken/box_underdetermined.rav) adds a second case
to `Box`'s data type and a constructor for it that takes no `T`-typed argument at all:

```raven
rep type S = data {
  case box(unwrap: T)
  case tag(flag: Bool)
}

func mkTag() returns (res: S) {
  tag(true)
}
```

`Box.mkTag()` fails, deliberately: `[Type Error] Cannot infer a type argument for parameter T of
Box; write an explicit instantiation, e.g. module M_X = Box[...]`. `tag(true)`'s payload is a
hardcoded `Bool` — nothing in the call mentions `T` at all, so there's nothing to unify it
against. Reaching for a type annotation instead doesn't rescue this: neither
`(Box.mkTag() : Box[Int])` nor `var n : Box[Int] := Box.mkTag()` helps, and both fail with that
exact same error. An inline instantiation like `Box[Int]`, written directly in a type position,
doesn't count as "an existing instantiation of `Box`" for inference to read a type argument back
off — it isn't, itself, a call whose arguments this mechanism examines. The message states the
only fix that actually works: fall back to an explicit instantiation, `module BoxTag =
Box[Library.IntType]`, and call `BoxTag.mkTag()` instead.

One sharp edge worth flagging alongside that fallback: an explicit instantiation and an implicit
one are *not* interchangeable, even at the exact same type argument — so an annotation naming an
*existing, already-declared* instantiation doesn't fully rescue `Box.mkTag()` either. Try
`var n : BoxTag.S := Box.mkTag()`: this time inference *does* solve `T := Int` (unlike `Box[Int]`
above, `BoxTag.S` already names a real instantiation), but the call still produces its own fresh,
separate implicit instantiation of `Box[Int]` to compute its result, and that fresh instantiation
is a different type from `BoxTag.S` — so the assignment fails, now with `Expected an expression of
type BoxTag.S but found an expression of type GenInst$$Box$$Int.S` instead. That
`GenInst$$Box$$Int` name is exactly the internal instantiation {{ref sec:implicit-functor-instantiation}} said you'd never have to spell
out yourself — until, as here, a type error spells it out for you. It's also exactly what
`Box.mk(3)` infers to on its own; mixing a `BoxTag.S` value with a `Box.mk(...)`-produced one hits
the identical mismatch, for the identical reason. Both are separately-declared instantiations of
one functor at identical arguments, and instantiation is generative by design: no annotation
makes two different instantiations into one.
Pick one mechanism per type argument you care about and stick to it — in practice, that usually
means: prefer implicit instantiation until inference genuinely can't determine a type argument
from a call's own arguments, and only then introduce one explicit, named instantiation, calling
through *that* consistently from that point on rather than mixing it with implicit calls.

## `import` {#sec:import}

`import C.valid` brings `valid` into unqualified scope inside `UseCounter`, so the body can write
`valid(c, 1)` instead of `C.valid(c, 1)`. You'll also see `import M._` elsewhere (not in this
file) to bring in *every* member of a module `M` at once, rather than naming them one at a time.

One sharp edge worth knowing about: if the importing module *also* declares a member with the
same name as something you `import`, the import silently loses — with no warning, and
regardless of which one appears first, textually. `import M.x` followed (or even preceded)
elsewhere by your own `val x: Int = 1` just makes the import a no-op for `x`; nothing tells you
it happened. This doesn't come up in this chapter's own examples, but it's the kind of thing
worth knowing exists before it costs you an afternoon.

## Rolling your own well-founded order {#sec:well-founded-order}

{{ref sec:termination-measure}} used a lexicographic `decreases m, n`, built from `Int`'s own built-in order. Every
`decreases` clause is secretly resolved this same way — by the *type* of whatever expression you
give it, which needs an instance of `Library.WellFoundedOrder`, an ordinary interface from the
standard library:

```raven
interface WellFoundedOrder : Type {
  func lt(x: T, y: T) returns (res: Bool)
  func embed(x: T) returns (res: OrdinalBase.T)

  axiom lt_embed_mono()
    ensures forall x: T, y: T :: {lt(x, y)} lt(x, y) ==> OrdinalBase.lt(embed(x), embed(y))
}
```

This is exactly {{ref sec:lemmas-and-axioms}}'s `axiom` pattern, one more time: implementing `WellFoundedOrder` means
supplying `lt`, and then either discharging `lt_embed_mono` yourself with a real `lemma` body,
or letting Raven attempt it automatically and fail if the fact doesn't actually hold. The
function `embed` is the mechanism that makes this checkable at all rather than merely assumed:
every instance has to map its own `T` into `Library.OrdinalBase.T` — ordinals in Cantor normal
form, the one well-founded structure this whole mechanism ultimately trusts. You then need to
prove that `embed` is a homomorphism for `lt` with the ordinal order. A pullback of a
well-founded relation is always well-founded, so this reduces *every* instance's
well-foundedness to one single trusted fact, rather than asking you to prove non-existence of
an infinite descending chain directly each time (which, for most interesting orders, is a much
harder thing to show from scratch).

Raven ships four instances of `WellFoundedOrder`: `Library.IntOrder` (what every plain-`Int`
`decreases` clause you've written so far actually resolves to), `Library.LexOrder[A, B]`
({{ref sec:termination-measure}}'s lexicographic combinator, generic over any two well-founded orders `A` and `B`),
`Library.Ordinal` (the raw ordinals themselves), and `Library.MultisetOrder` (for a termination
argument shaped like "some multiset only ever shrinks," which no fixed-arity lexicographic
tuple can express — see `lib/ext/decreasesExt/well_founded_order.rav` if you want the
details). There's a fifth built-in option you may already have seen or used without noticing:
write `decreases` on a value of a self-recursive `data` type (a `List[E]`'s tail, a tree's
child), and Raven auto-generates a structural "subterm" order on the fly: `x` counts as smaller
than `y` exactly when `x` is one of the pieces `y` was built from. This is what makes
straightforward structural recursion over your own recursive algebraic data types just work
without you ever having to reach for this section. If your own measure doesn't fit any of
these, you implement `WellFoundedOrder` yourself, exactly like implementing any other
interface. [`well_founded_order.rav`](./well_founded_order.rav) is a minimal complete example —
a two-state "not done yet"/"done" order, collapsing towards `true`:

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

One easy-to-miss detail, worth calling out because it's cost people real debugging time before:
`rep type T` is defined as a one-case wrapper around `Bool`, not `rep type T = Bool` directly.
A `rep type` alias to a type from *outside* the module resolves transparently to that other
type's own identity once elaborated. So a bare alias here would make a `decreases` clause of
this type quietly resolve to plain `Bool` (which has no `WellFoundedOrder` instance at all)
rather than to `BoolOrder`. `Library.Ordinal`, in the standard library itself, wraps
`Library.OrdinalBase.T` for exactly this same reason.

## Why this matters for concurrency

Every lock and every concurrent data structure from Part 4 uses the module system to
parameterize proofs and implementations *exactly* this way. In particular, a lock abstracts
over an abstract resource it protects, left as abstract as `Counter`'s `valid` is here. The
`LockResource`/`Lock` interface split you'll meet in Part 5 is this chapter's pattern, applied
to threads instead of sequential callers. Part 5a's fork/join capstone pushes the same pattern
one step further: its `Instance` interface abstracts over not just a resource, but an entire
*computation* that produces one (`proc task() returns (r: R) ensures resource(r)`): the functor
parameterizes an actual piece of behavior, not only a specification. Similarly, client code of
a `Lock` can abstract over the lock implementation, which itself abstracts over the protected
resource that is provided by the client code, exploting the fact that the module system
supports *higher-order* functors.

## Debugging Corner

An axiom your module couldn't auto-discharge doesn't get its own special diagnostic — an axiom
is just a body-less lemma, so its failure looks exactly like an ordinary failed
precondition/postcondition, anchored at the axiom's *declaration site inside the interface*
rather than at any call site in your own code. That location is the tell: when a diagnostic
points into an interface you didn't write, rather than into your module's own body, that's your
signal it's an inherited obligation, not a bug in the code you just wrote — and the fix is a
proof (an explicit `lemma`, as in {{ref sec:lemmas-and-axioms}}).

## Exercise

[`exercises/sum_counter.rav`](./exercises/sum_counter.rav): finish the `Sum[A: Counter, B:
Counter]` functor, which combines two counters into one whose value is their sum, without ever
looking at `A`'s or `B`'s internals. `create` is done for you as a worked example of the
fold-with-witnesses syntax (`valid`'s body existentially quantifies over each side's own value,
and `fold`/`unfold ... [va := ..., vb := ...]` is how you supply or capture those existentials).
Finish `increment`, `get`, and the `nonNegative` proof. A checked solution is in
[`solutions/sum_counter.rav`](./solutions/sum_counter.rav) — its comments walk through exactly
the "hand the resource back" subtlety from {{ref sec:lemmas-and-axioms}}, which resurfaces here in a sharper form once
you're chaining two sub-proofs together instead of just unfolding your own predicate.

## What's next

[Part 4](../ghost-and-concurrency/) is where this all starts paying off differently: the
counter goes concurrent, and Parts 2–3's ownership and module machinery turn out to be exactly
what's needed to reason about it under arbitrary thread interleavings.
