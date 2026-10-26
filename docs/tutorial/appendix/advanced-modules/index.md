# Advanced Module Features

*Assumes: Part 3's interfaces, functors, and {{ref sec:implicit-functor-instantiation}}.*

The module chapter introduces the common forms. This appendix covers the additional inference
rules, type identities, generative factories, and sealing forms that matter when building
reusable libraries.

## Eligibility and inference {#sec:module-inference-details}

Implicit instantiation is checked structurally. For type-based inference, each functor parameter
must be constrained by an interface declaring a `rep type`; `Library.Type` and `Counter` both
qualify. The basic `Box.mk` and `Box.get` example is in
[`implicit_instantiation.rav`](../../modules/implicit_instantiation.rav).

Eligibility does not guarantee that a particular call contains enough information. Inference
can use argument types and, for functions, an expected result type. Consider a constructor
function whose arguments do not mention the functor's type parameter:

```raven
module Box[T: Library.Type] {
  rep type S = data {
    case box(unwrap: T)
    case tag(flag: Bool)
  }

  func mkTag() returns (res: S) { tag(true) }
}
```

`var n := Box.mkTag()` leaves `T` undetermined. The checked failure example
[`broken/box_underdetermined.rav`](./broken/box_underdetermined.rav) reports
`Cannot infer a type argument for parameter T of Box; write an explicit instantiation`.
The `Bool` payload of `tag` supplies no information about `T`.

An expected result type can supply the missing information:

```raven
val tag: Box[Int] := Box.mkTag();
```

Here, `Box[Int]` identifies the canonical integer instance, and the call uses it. The same
works with an expression annotation, `(Box.mkTag() : Box[Int])`. You can also instantiate
explicitly and call the member through that module:

```raven
module BoxTag = Box[Int]
```

`BoxTag.mkTag()` needs no inference. An expected type naming this existing instance also works:
`val tag: BoxTag.S := Box.mkTag();`. These successful forms are checked in
[`inference.rav`](./inference.rav).

A parameter can also be inferred from a location argument when its interface declares exactly
one field and no other abstract members apart from module members. The field comes from the
location, and its value type determines those module members. This is the additional inference
form used by generic atomic operations; type-based inference remains the usual case for
collection libraries. If any parameter has neither a supported rep type nor this field-interface
shape, write an explicit instantiation.

## Instance identity {#sec:module-instance-identity}

Ordinary functor applications are applicative: the same functor applied to the same module
arguments shares one canonical instance. This applies to explicit declarations, inferred calls,
and type notation alike. Thus `module BoxTag = Box[Int]` names the same instance that
`Box.mk(3)` and the type `Box[Int]` use; `BoxTag.S` and `Box[Int]` are the same type.
`Box.mk(true)` uses a different instance. Module aliases preserve identity, while distinct
named argument modules remain different arguments even if both represent the same type.

This extends to instances written inside a functor. If a functor `G[E: Library.Type]` uses
`Box[E]`, then in an instance `module GI = G[Int]` that is the same instance as `Box[Int]`, so a
value of type `Box[Int]` can be passed where a member of `GI` expects a `Box[E]`, as in
[`inference.rav`](./inference.rav). The call `G.flag(b)` infers that instance from the argument
alone, as `E` occurs in `b`'s type `Box[Int]`.

Argument types or an expected result type can identify an existing instance for a call.
`Box.get(b)` reads that identity from `b`, and `val tag: BoxTag.S := Box.mkTag()` selects the
integer instance from the expected result type. Conflicting evidence for distinct module
arguments cannot merge their nominal types. Use a unit-parameter factory when separate
applications must introduce fresh identities, as described next.

When a call has insufficient context, qualify it through the intended module. This also avoids
relying on contextual inference for constructors or other member forms whose inference rules
are more limited than ordinary function calls.

## Generative factories {#sec:module-generative-factories}

A unit parameter, written `()`, requires a fresh application. In
[`unit_factories.rav`](./unit_factories.rav), `Tokens` declares a nominal token type:

```raven
module Tokens() {
  type T = data { case token(value: Int) }
}
module First = Tokens()
module Second = Tokens()
module Alias = First
```

`First.T` and `Second.T` are distinct types. An alias introduces no new instance,
so a `First.T` value can also be used as an `Alias.T`. A manifest equation such
as `type T = Int` keeps that equality even in fresh instances.

An interface can declare the same unit parameter, for example
`interface Factory() { type T }`. A parameter `F: Factory` denotes an unapplied
factory; use `module Value = F()` before accessing its result members. Raven never
inserts `()` through inference. A named-parameter functor can define a nested
factory for its clients to apply.

Factories may apply other factories. A named-parameter functor may also apply a factory
when the visible result introduces no fresh nominal type, field, predicate, invariant, or
atomic-update procedure. The check follows inherited and nested members, sealing, and local
module applications. Aliases to existing resources and shared external functor instances
preserve their identities and are allowed.

For example, this composition is accepted (also checked in
[`unit_factories.rav`](./unit_factories.rav)):

```raven
module Helpers() {
  type T = Int
  val one: T = 1
  func increment(x: T) returns (r: T) { x + one }
}
module UsesHelpers[E: Library.Type] {
  module H = Helpers()
  func increment(x: Int) returns (r: Int) { H.increment(x) }
}
```

The result may contain ordinary procedures and lemmas. Unspecified values and bodyless
functions are conservatively rejected because they introduce unconstrained logical symbols;
recursive module result shapes are also rejected.
Formal factories are checked through their declared interfaces, and abstract result types
remain fresh even if a concrete implementation uses a manifest type. Nested unapplied
functors are checked conservatively too, including nominal declarations in their results.
This rule remains stricter than OCaml's restriction on fresh types alone, since Raven also
has nominal resources and atomic updates.

Seal factory declarations, unapplied aliases, or individual applied results, as described below.

## Generic default values {#sec:module-default-values}

`Library.Type`, the standard library's interface for "any type", declares one more member
besides `rep type T`: a value `default: T`. It gives generic code some value of `T` to fall back
on, for instance as the result of a `func` on inputs where there is nothing meaningful to
return. The value is deliberately unspecified. You can't prove anything about it beyond its
type, so for `module IntOption = Library.Option[Int]`, even `assert IntOption.E.default == 0`
fails. `default` is declared `free`, which means an implementation of `Library.Type` doesn't
have to define it and simply inherits it. A module that wants a specific value can still define
`val default: T = ...` itself. Leaving it
undefined is sound because every Raven type is backed by a non-empty SMT sort, so some value of
`T` always exists.

## Types as interface arguments {#sec:module-type-arguments}

A module can implement an instance of a parameterized interface for a particular type. The
argument can be the type itself, as in [`type_arguments.rav`](./type_arguments.rav):

```raven
module CountingStack : Stack[Int] {
  rep type T = Int
  val empty: T = 0
  func push(s: T, e: Int) returns (ret: T) { s + 1 }
  func size(s: T) returns (ret: Int) { s }
}
```

`Stack`'s parameter `E` is constrained by `Library.Type`, and Raven supplies the module that
implements `Library.Type` for `Int`, the same one that `Box[Int]` uses. Inside the interface's
members, `E` then stands for `Int`, which is why `push` takes an `Int`.

## Sealing modules and individual instances {#sec:module-sealed-views}

{{ref sec:sealing}} introduces sealed functors: every instance exposes only its interface,
whether created explicitly, inferred from a call, or written in a type position. The functor's
own body can still use its representation. A sealed module names exactly one interface.

A module without parameters can be sealed the same way. Outside its own body, `module M :> I {
... }` shows only the members of `I`, and its abstract types are distinct from every other type.
You can also seal a single instance of a module that implements an interface: `module V :> I = N`
makes `V` a view of `N` through `I`, and `module V :> Stack = F[Int]` does the same
for an instance of a functor `F`. `N` or `F` has to declare that it implements the interface, and Raven
takes the interface's arguments from that declaration. Code that names `N` directly still sees
its definitions, but to clients of `V`, `V.T` is an abstract type, distinct from `N.T`.

### Sealing unapplied functors

An unapplied functor can also be given a sealed view, as checked in
[`functor_aliases.rav`](./functor_aliases.rav):

```raven
module Hidden :> Box = Implementation
module First = Hidden[Int]
module Second = Hidden[Int]
module Alias = Hidden
```

The target must already implement the selected interface nominally. The alias keeps the
target's input parameters, including their order and constraints, and exposes the interface
at the result arguments declared by the target. For example, if `Implementation[X, Y]`
implements `Box[Y]`, then `Hidden[Int, Bool]` exposes the boolean box interface.
The interface can also be unparameterized or an already applied interface alias.

Repeated named applications through `Hidden` or `Alias` share their abstract result types.
Those types are distinct from the original implementation's types and from those of a
separate sealed view of the same implementation. Manifest equations stated in the interface
remain visible. Unit-parameter targets retain `()` syntax and produce a fresh result at
each application, including applications through aliases. Higher-order parameters can use
these views through their compatible nominal interfaces. Higher-order compatibility
also checks that the input constraints and parameter-to-result mapping agree: a functor
returning `Box[Int]` for every input cannot stand for one returning `Box[E]` for input `E`.

The source implementation remains available through its original name, with its original
representation and additional members. Creating a view does not verify a second copy of its
body. Interfaces can also be viewed this way as assumed API models, consistent with
ordinary interface instantiation in Raven.

## Checked module views {#sec:module-checked-views}

Ordinary module arguments must implement their required interface nominally: a matching set of
members alone does not establish conformance. An explicit checked view adapts an existing
module and verifies the required contracts:

```raven
interface Positive {
  proc next(x: Int) returns (r: Int) requires x >= 0 ensures r > x
}
module Counter {
  proc next(x: Int) returns (r: Int) ensures r == x + 1 { r := x + 1; }
}
module View : Positive = checked Counter
module Client[M: Positive] { }
module Accepted = Client[View]
```

This example is checked in [`checked_views.rav`](./checked_views.rav). `Client[Counter]` still
requires a nominal implementation declaration; creating `View` does not add one to `Counter`.
If the target already implements the requested interface, the binding uses ordinary nominal
checking and preserves its callable identities without generating adapters.

Otherwise, Raven generates forwarding functions, procedures, and lemmas and verifies them
against the interface through its usual proof pipeline. Logically atomic procedures forward
through an atomic update, including its abort-restoration obligations. Physically atomic
requirements must be satisfied by physically atomic target procedures. The adapter does not
coerce atomic update tokens between different procedures.

Types, fields, predicates, and invariants share their target identities through transparent
aliases. Resource aliases can also be written explicitly, as `pred p(x: Ref) = Actual.p` or
`inv shared(x: Ref) = Actual.shared`; their signatures and parameter modes must match. Field
constraints must agree in both directions. Writing `module View :> Positive = checked Counter`
adds ordinary sealing, so clients see the interface's abstract representation.

The target must name an instantiated structure: bind a functor application first, then adapt
that binding. Parameterized interfaces and abstract nested module members are supported.
Structural adaptation currently requires explicit adapters for interface-defined data types,
defined values or callables, concrete nested module definitions, extension contract clauses,
and public signatures exposing atomic update tokens. These restrictions do not affect the
nominal fast path.
