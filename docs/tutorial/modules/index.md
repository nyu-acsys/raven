# 3. The Module System

This part does not add any new *reasoning* principle. Everything here is still ordinary
sequential ownership from Part 2. What's new is *organization*: hiding a representation behind
an interface, giving that interface more than one implementation, and composing implementations
with functors. All code below is in
[`counter_interface.rav`](./counter_interface.rav), verified as a whole.

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
has no definition, `pred valid` has no body, and the `proc`s have no implementation. `rep type`
marks `T` as the interface's *representation type*. The benefit is that anywhere a type is
expected, you can write the module's own name and Raven expands it to `Counter.T` for
you. That's why `Counter`'s procedures can write `c: T` and, once you get to `UseCounter[C:
Counter]` below, callers can write `c: C` within `UseCounter` rather than spelling out `c: C.T`
everywhere.

`pred valid(c: T, v: Int)` is the `pred counter` from {{ref sec:bundling-pred}} with the body
removed. There, `counter`'s body, `own(c.count, v) && v >= 0`, was visible to anyone reading the
declaration, and `fold`/`unfold` against it were legal anywhere that body was in scope.
Here, `valid` is only a *signature*: a name and a parameter list, nothing else. An interface can
declare that a predicate exists and what it's parameterized over, but never what it actually
asserts. What it asserts is exactly the representation-specific detail that no client of
`Counter` should be able to depend on. This has a direct consequence for `fold`/`unfold`.
Both need the body to check what they're consuming or producing, so neither one can be used on
`valid` outside of a module that has actually supplied that body. Folding or unfolding it only
becomes possible once a `module M : Counter` gives `valid` a real definition (see
{{ref sec:implementing-interface}}, next), and then only *inside* `M`, since the body is not in
scope anywhere else.

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

`module M : I { ... }` is a promise that every abstract member of `I` gets a real definition in
`M`. Raven checks that the contract of each one matches what `I` declared. Here, the body of
`valid` is exactly the `counter` predicate from {{ref sec:bundling-pred}}. `PlainCounter` is the
same running example, now supplying the body that its interface withheld. From this point on,
`PlainCounter`'s own `create`/`increment`/`get` can `fold`/`unfold` `valid` exactly the way Part
2's `make`/`bump` did. Note that `:` doesn't hide anything by itself. Code that names
`PlainCounter` directly still sees the body of `valid` and could unfold it too. Information
hiding comes from writing clients against the interface instead, as
{{ref sec:abstract-predicates}} explains, or from sealing a functor, as
{{ref sec:sealing}} explains.

## Abstract predicates as a specification boundary {#sec:abstract-predicates}

The reason for leaving `valid` abstract in the interface is that a client can never look
past it. [`counter_interface.rav`](./counter_interface.rav) has *two* implementations:
`PlainCounter`, the direct Part 2 representation, and `OffsetCounter`, which stores `v + 1000`
in its one field instead of `v` directly. They share nothing at the representation level. Yet
`UseCounter[C: Counter]`'s `demo` procedure is written once, against `Counter` alone, and
verifies identically whether `C` is instantiated to `PlainCounter` or `OffsetCounter`. Take a
look at the two `module UsePlain = ...` / `module UseOffset = ...` lines at the bottom of the
file. This is what "abstract predicate as a specification boundary" means concretely: `valid` is
the entire interface between a `Counter`'s clients and its internals, in both directions.

## Lemmas and axioms {#sec:lemmas-and-axioms}

A `lemma` is Raven's proof-only callable. Syntactically, it is almost a `proc` (same
parameters, same `requires`/`ensures`, a statement-based body), but with two restrictions
that make it about proof rather than computation. First, like a `func`, it must terminate. Raven
silently *assumes* this by default rather than checking it, unless you give the lemma a
`decreases` clause (the same discipline, and the same advice, as in {{ref sec:control-flow}}).
Second, and more fundamentally, a `lemma` can never affect the *running* program. It can never
call an ordinary `proc` or `spawn` a thread (if you try, you get `[Type Error] Cannot call
procedure in ghost context`). The entire callable, body included, disappears before compilation,
just like every other ghost construct you've seen since Part 2.

This erasure is the key to understanding what a `lemma` actually *is*. Its body is never
executed. It's a proof, written in the form of a program, that the verifier walks through step by
step to justify a logical fact (the lemma's own contract), the same way the steps of a
mathematical proof justify a theorem. This is the "programs as proofs" idea in miniature. Raven
checks a `lemma`'s body using the same machinery it uses to check a `proc`'s, but the result is
never compiled or run.

With `lemma` understood, **an axiom is a lemma with no body**. In other words, it is a proof
obligation you're stating but not (yet) discharging, an assumption rather than an established
fact. The two are interchangeable. The `axiom` keyword just makes the "this is an assumption"
reading explicit at the declaration site. When a module implements an interface that declares
an axiom, that axiom has to become an established fact for *this particular module*. You have
two options to do so. You can supply it as a `lemma` with the same name and contract, but now
with a real proof body. Alternatively, if you don't provide an implementation for it, Raven
automatically attempts to discharge the axiom's exact statement on its own, ultimately handing
it to the SMT solver with no help from you:

```raven
axiom nonNegative(c: T, ghost v: Int)
  requires valid(c, v)
  ensures valid(c, v) && v >= 0
```

Try deleting the `lemma nonNegative { ... }` block from `PlainCounter` and re-verifying. Raven's
automatic attempt **fails**, even though "a counter's value is never negative" looks obvious. The
reason is that `valid` is an opaque, foldable predicate as far as the verifier is concerned.
Nothing *inside* it (here, the fact that its definition includes `v >= 0`) is visible to a proof
unless something explicitly `unfold`s it first. So every implementation supplies its own proof,
as a `lemma` with exactly the same name and contract as the axiom. Here, `unfold valid(c, v);
fold valid(c, v);` is enough, since unfolding is what exposes the `v >= 0` conjunct, and folding
immediately afterwards hands the resource back to the caller. That last step matters. An axiom
about a resource should generally hand the resource back in its `ensures` (notice that
`nonNegative`'s `ensures` includes `valid(c, v)`, not just `v >= 0`), unless it's deliberately
meant to consume it. The Sum exercise below shows you *why* if you skip this.

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
specializing procedure `demo` to `PlainCounter`. This is the mechanism that lets a proof be
written once and reused for every implementation of an interface, rather than being copied for
each implementation. Here, the `assert` statements in `demo` are that proof.

Let's be precise about what has been proved once both instantiations exist. The module system
isn't just abstracting over *proofs* here. It's abstracting over a real *implementation*,
parametric in another implementation. `UseCounter` itself is implemented, and proved correct,
exactly *once*, against `Counter` alone. Separately, `PlainCounter` and `OffsetCounter` are each
implemented and proved correct exactly once, against `Counter`'s contracts, for *every* way
either one might ever be used, not just this particular `demo`. `UsePlain` and `UseOffset` then
simply compose these finished proofs. Instantiating `UseCounter[PlainCounter]` doesn't require
Raven (or you) to discharge any further proof obligation, because none is left. The functor's
proof already covers any `Counter`, and `PlainCounter` already comes with a proof that it is one.

## Implicit functor instantiation {#sec:implicit-functor-instantiation}

Every functor use so far has needed an explicit instantiation, such as `module UsePlain =
UseCounter[PlainCounter]`, before anything could be called through it. Raven can skip that step
and infer the instantiation for you at the call site, provided that *every* formal of the
functor is constrained by an interface that itself declares a `rep type`. `Counter` has this
shape, as will any interface built the way {{ref sec:interfaces-and-modules}} describes. The
following code is [`implicit_instantiation.rav`](./implicit_instantiation.rav), a self-contained
example:

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

`Box.mk(3)` never instantiates `Box` by name anywhere. `mk`'s formal is declared `a: T`, where
`T` is `Box`'s own, still-abstract formal, and the actual argument `3` has type `Int`. Unifying
the two solves `T := Int`, and Raven silently instantiates `Box[Int]` on your behalf, under an
internal name you never see or write. `Box.get(b)` is resolved in a similar way, but from the
other direction. `get`'s parameter is typed `S`, `Box`'s own rep type, so instead of unifying
against a plain argument, Raven reads the type argument directly off `b`'s inferred type. The
same mechanism covers destructor syntax too. `b.Box.unwrap` resolves identically, without you
ever having written down which instantiation of `Box` `b` belongs to.

`Library.Type`, the standard library's interface for "any type", declares one more member
besides `rep type T`: a value `default: T`. It gives generic code some value of `T` to fall back
on, for instance as the result of a `func` on inputs where there is nothing meaningful to
return. The value is deliberately unspecified. You can't prove anything about it beyond its
type, so even `assert Library.IntType.default == 0` fails. `default` is declared `free`, which
means an implementation of `Library.Type` doesn't have to define it and simply inherits it. A
module that wants a specific value can still define `val default: T = ...` itself. Leaving it
undefined is sound because every Raven type is backed by a non-empty SMT sort, so some value of
`T` always exists.

Calling `Box.mk(3)` a second time resolves to the *same* implicit instantiation as the first.
Raven deduplicates by the inferred type argument, so the results of both calls share one type and
can be compared with `==`. A call with a different inferred argument, like `Box.mk(true)`, gets
its own separate instantiation, coexisting with `Box[Int]` in the same proc.

Eligibility is checked structurally, not by name. A functor qualifies if "every formal's
constraining interface has a `rep type`," which is why `Library.Type` (`Box`'s constraint on
`T`) and `Counter` both work, since both declare one. `UseCounter` itself, from
{{ref sec:functors}}, technically qualifies in the same way, since `Counter` has a `rep type`.
However, `demo` takes no arguments at all, so a call to `UseCounter.demo()` gives Raven nothing to
infer `C` from, and you're back to writing `UseCounter[PlainCounter]` explicitly. If a formal's
constraining interface has no `rep type` in the first place, the functor doesn't qualify at all.
A bare `F.member` then fails with the ordinary "unknown identifier" error, exactly as if `F` were
never declared to have a member `member`, because without an instantiation it doesn't have one.

Inference can fail even for an eligible functor when nothing about a call pins down a formal.
[`broken/box_underdetermined.rav`](./broken/box_underdetermined.rav) adds a second case to
`Box`'s data type and a constructor for it that takes no `T`-typed argument at all:

```raven
rep type S = data {
  case box(unwrap: T)
  case tag(flag: Bool)
}

func mkTag() returns (res: S) {
  tag(true)
}
```

`Box.mkTag()` fails, as intended: `[Type Error] Cannot infer a type argument for parameter T of
Box; write an explicit instantiation, e.g. module M_X = Box[...]`. The payload of `tag(true)` is
a hardcoded `Bool`, and nothing in the call mentions `T` at all, so there's nothing to unify it
against. Adding a type annotation doesn't fix this either. Neither
`(Box.mkTag() : Box[Int])` nor `var n : Box[Int] := Box.mkTag()` helps, and both fail with the
same error. An inline instantiation like `Box[Int]`, written directly in a type position,
doesn't count as an existing instantiation of `Box` that inference could read a type argument
from, because it isn't a call whose arguments this mechanism examines. The message states the
only fix that works: fall back to an explicit instantiation, `module BoxTag =
Box[Library.IntType]`, and call `BoxTag.mkTag()` instead.

There's a pitfall to be aware of with this fallback. An explicit instantiation and an implicit
one are *not* interchangeable, even for the same type argument. This means that an annotation
naming an *existing, already-declared* instantiation doesn't fully fix `Box.mkTag()` either. Try
`var n : BoxTag.S := Box.mkTag()`. This time inference *does* solve `T := Int` (unlike `Box[Int]`
above, `BoxTag.S` already names a real instantiation). However, the call still produces its own
fresh, separate implicit instantiation of `Box[Int]` to compute its result, and that fresh
instantiation is a different type from `BoxTag.S`. So the assignment fails, now with `Expected an
expression of type BoxTag.S but found an expression of type GenInst$$Box$$Int.S` instead. The
name `GenInst$$Box$$Int` is the internal instantiation that, as mentioned earlier in this
section, you normally never have to spell out yourself, until a type error like this one shows
it to you. It's also exactly what `Box.mk(3)` infers on its own. Mixing a `BoxTag.S` value with
one produced by `Box.mk(...)` causes the same mismatch, for the same reason. Both are separately
declared instantiations of one functor with identical arguments, and instantiation is generative
by design. No annotation makes two different instantiations into one.
Choose one mechanism per type argument you care about and stick to it. In practice, this usually
means preferring implicit instantiation until inference can't determine a type argument from a
call's own arguments. Only then should you introduce one explicit, named instantiation, and from
that point on call through *that* instantiation consistently rather than mixing it with implicit
calls.

## Sealing a functor {#sec:sealing}

Writing a client as a functor over an interface, as `UseCounter` does, keeps that client from
depending on any implementation's internals. Sealing gives the same guarantee to *every* client of
a functor, including ones that instantiate it directly. A functor declared with `:>` instead of
`:` is sealed: outside its own definition, each of its instances shows only the members of its
interface. The following code is [`sealing.rav`](./sealing.rav):

```raven
interface Stack[E: Library.Type] : Library.Type {
  rep type T
  val empty: T
  func push(s: T, e: E) returns (ret: T)
  func size(s: T) returns (ret: Int)

  auto lemma size_empty()
    ensures size(empty) == 0

  auto lemma size_push()
    ensures forall s: T, e: E :: {size(push(s, e))} size(push(s, e)) == size(s) + 1
}

module ListStack[E: Library.Type] :> Stack[E] {
  rep type T = data {
    case nil
    case cons(hd: E, tl: T)
  }

  val empty: T = nil

  func push(s: T, e: E) returns (ret: T) {
    cons(e, s)
  }

  func size(s: T) returns (ret: Int)
    decreases s
  {
    s == nil ? 0 : 1 + size(s.tl)
  }
}

module Client {
  module S = ListStack[Library.IntType]

  lemma two_pushes()
  {
    assert S.size(S.push(S.push(S.empty, 1), 2)) == 2;
  }
}
```

Raven checks `ListStack` against `Stack` once, for every `E`, exactly as for `:`. Here, it proves
both auto lemmas from the definitions on its own. To `Client`, however, `S.T` is an abstract type,
and `push` and `size` have no bodies. `two_pushes` verifies using `size_empty` and `size_push`
alone. The constructors are out of reach: writing `S.nil` fails with `nil is not accessible here:
S is an instance of the sealed module ListStack, which exposes only the members of interface
Stack`. So `Client` can't depend on the list representation, and `ListStack` can switch to a
different one without breaking it, as long as it still proves `Stack`'s lemmas.

Sealing also helps verification performance. With `:`, the body of every `func` reaches the
SMT solver as a definition axiom in every proof that mentions the `func`. For recursive functions,
such axioms can make the solver unfold definitions over and over. A sealed functor's clients see
only the interface's lemmas, with the triggers its author chose for them.

Every instance of a sealed functor is sealed, whether it is declared explicitly as above,
inferred from a call ({{ref sec:implicit-functor-instantiation}}), or written as a type such as
`ListStack[Int]`. Only the functor's own body sees through the seal. There are three
restrictions. Only a functor (a module with parameters) can be sealed. It names exactly one
interface. And the seal belongs to the functor's definition, so `module M :> I = F[A]` is
rejected.

## `import` {#sec:import}

`import C.valid` brings `valid` into unqualified scope inside `UseCounter`, so the body can write
`valid(c, 1)` instead of `C.valid(c, 1)`. You'll also see `import M._` elsewhere (not in this
file), which brings in *every* member of a module `M` at once rather than naming them one at a
time.

There is one pitfall worth knowing about. If the importing module *also* declares a member with
the same name as something you `import`, the import silently loses. There is no warning, and it
doesn't matter which one appears first in the text. `import M.x` followed (or even preceded)
elsewhere by your own `val x: Int = 1` just makes the import a no-op for `x`, and nothing tells
you that this happened. It doesn't come up in this chapter's examples, but it's good to be aware
of it before it costs you an afternoon.

## Rolling your own well-founded order {#sec:well-founded-order}

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

## Why this matters for concurrency

Every lock and every concurrent data structure from Part 4 uses the module system to
parameterize proofs and implementations in *exactly* this way. In particular, a lock abstracts
over the resource it protects, which is left as abstract as `Counter`'s `valid` is here. The
`LockResource`/`Lock` interface split you'll meet in Part 5 is this chapter's pattern applied to
threads instead of sequential callers. Part 5.1's fork/join capstone takes the same pattern one
step further. Its `Instance` interface abstracts over not just a resource but an entire
*computation* that produces one (`proc task() returns (r: R) ensures resource(r)`), so the
functor parameterizes an actual piece of behavior, not only a specification. Similarly, client
code of a `Lock` can abstract over the lock implementation, which itself abstracts over the
protected resource provided by the client code. This relies on the module system's support for
*higher-order* functors.

## Debugging Corner

An axiom that your module couldn't discharge automatically doesn't get its own special
diagnostic. An axiom is just a body-less lemma, so its failure looks exactly like an ordinary
failed precondition/postcondition, anchored at the axiom's *declaration site inside the
interface* rather than at any call site in your own code. That location is the clue. When a
diagnostic points into an interface you didn't write, rather than into your module's own body,
it signals an inherited obligation rather than a bug in the code you just wrote. The fix is a
proof (an explicit `lemma`, as in {{ref sec:lemmas-and-axioms}}).

## Exercise

[`exercises/sum_counter.rav`](./exercises/sum_counter.rav): finish the `Sum[A: Counter, B:
Counter]` functor, which combines two counters into one whose value is their sum, without ever
looking at the internals of `A` or `B`. `create` is done for you as a worked example of the
fold-with-witnesses syntax (`valid`'s body existentially quantifies over each side's own value,
and `fold`/`unfold ... [va := ..., vb := ...]` is how you supply or capture those existentials).
Finish `increment`, `get`, and the `nonNegative` proof. A checked solution is in
[`solutions/sum_counter.rav`](./solutions/sum_counter.rav). Its comments walk through the
"hand the resource back" subtlety from {{ref sec:lemmas-and-axioms}}, which resurfaces here in a
sharper form because you're chaining two sub-proofs together instead of just unfolding your own
predicate.

## What's next

In [Part 4](../ghost-and-concurrency/) the counter becomes concurrent. The ownership and module
machinery from Parts 2–3 turns out to be exactly what's needed to reason about it under arbitrary
thread interleavings.
