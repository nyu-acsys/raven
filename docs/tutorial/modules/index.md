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
  // ... create/increment/get, with Counter's contracts
}
```

`module M : I { ... }` is a promise that every abstract member of `I` gets a real definition in
`M`. A member of `M` can repeat the contract that `I` declared for it, and Raven then checks that
the two match exactly. It can also omit its contract altogether, with no `requires`, `ensures` or
`opens`, and inherit `I`'s, with `I`'s names for the parameters replaced by its own. This way, a
change to a contract in `I` needs no change in `M`. Here, the body of
`valid` is exactly the `counter` predicate from {{ref sec:bundling-pred}}. `PlainCounter` is the
same running example, now supplying the body that its interface withheld. From this point on,
`PlainCounter`'s own `create`/`increment`/`get` can `fold`/`unfold` `valid` exactly the way Part
2's `make`/`bump` did. Note that `:` doesn't hide anything by itself. Code that names
`PlainCounter` directly still sees the body of `valid` and could unfold it too. Information
hiding comes from writing clients against the interface instead, as
{{ref sec:abstract-predicates}} explains, or from sealing a module, as
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
and infer the instantiation from the types at the call site. For this type-based inference,
each functor parameter must be constrained by an interface declaring a `rep type`, as
`Library.Type` and `Counter` are. The following code is
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

`Box.mk(3)` never instantiates `Box` by name anywhere. `mk`'s formal is declared `a: T`, where
`T` is `Box`'s own, still-abstract formal, and the actual argument `3` has type `Int`. Unifying
the two solves `T := Int`, and Raven silently instantiates `Box[Int]` on your behalf, under an
internal name you never see or write. `Box.get(b)` is resolved in a similar way, but from the
other direction. `get`'s parameter is typed `S`, `Box`'s own rep type, so instead of unifying
against a plain argument, Raven reads the type argument directly off `b`'s inferred type. The
same mechanism covers destructor syntax too. `b.Box.unwrap` resolves identically, without you
ever having written down which instantiation of `Box` `b` belongs to.

Applications of the same functor to the same module arguments share an instance, whether
written explicitly or inferred. For example, `module IntBox = Box[Int]` names the same instance
that `Box.mk(3)` uses, so their values have the same type. Aliases preserve that identity.
When Raven cannot infer a parameter, write an explicit instantiation.

{{ref app:advanced-modules}} covers inference from expected result types, unresolved parameters,
instance identity, generative factories, and the generic `default` value.

## Sealing modules {#sec:sealing}

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
  module S = ListStack[Int]

  lemma two_pushes()
  {
    assert S.size(S.push(S.push(S.empty, 1), 2)) == 2;
  }
}
```

Raven checks `ListStack` against `Stack` once, for every `E`, exactly as for `:`. Here, it proves
both auto lemmas from the definitions on its own (see {{ref sec:auto-lemmas}}). To `Client`, however, `S.T` is an abstract type,
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
`ListStack[Int]`. Only the functor's own body sees through the seal. A sealed module names
exactly one interface.

Single-instance sealing and other forms are described in {{ref sec:module-sealed-views}}.

The standard library's sequences, `Library.Seq`, are a sealed functor as well. {{ref app:stdlib-types}}
describes them, along with the library's other data types.

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
