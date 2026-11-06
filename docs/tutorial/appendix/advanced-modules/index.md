# Advanced Module Features

*Assumes: Part 3's interfaces, functors, and {{ref sec:implicit-functor-instantiation}}.*

The module chapter introduces the common forms. This appendix covers the additional inference
rules, type identities, generative factories, and sealing forms that matter when building
reusable libraries.

## Determining parameters {#sec:module-inference-details}

Implicit instantiation solves each functor parameter at each call. A call can determine a
parameter in two ways: from types, if the parameter's interface declares a `rep type`, as
`Library.Type` and `Counter` do, or from a location argument, if its interface declares a single
field, as described below. A parameter whose interface has neither is never inferred, and a call
through the functor's name reports `Cannot infer parameter S of F: its interface declares
neither a rep type nor a single field`; instantiate such a functor explicitly. The basic
`Box.mk` and `Box.get` example is in
[`implicit_instantiation.rav`](../../modules/implicit_instantiation.rav).

Even a parameter whose interface declares a `rep type` can be left undetermined by a particular
call. Inference uses the types of the call's arguments and, when the member is a function, the
type that the context expects of its result. Consider a function whose arguments do not mention
the functor's type parameter:

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

Here, the declared type `Box[Int]` determines `T := Int`, so the call uses the instance
`Box[Int]`. A type annotation on the expression works the same way:
`(Box.mkTag() : Box[Int])`. You can also instantiate `Box` explicitly and call the member through
the resulting module:

```raven
module BoxTag = Box[Int]
```

`BoxTag.mkTag()` needs no inference. The expected type can also name `BoxTag`'s type:
`val tag: BoxTag.S := Box.mkTag();`. These forms are checked in
[`inference.rav`](./inference.rav).

A parameter can also be inferred from a location argument when its interface declares exactly
one field and, apart from abstract module members, no other abstract members. The call's
location argument supplies the field, and the field's value type determines the interface's
abstract module members. Generic atomic operations use this form of inference; collection
libraries usually rely on inference from types.

## Instance identity {#sec:module-instance-identity}

Ordinary functor applications are applicative: applying the same functor to the same module
arguments always yields the same instance, whether the application is a module declaration,
is inferred from a call, or is written in a type. Thus `module BoxTag = Box[Int]` names the
same instance that the type `Box[Int]` names and that the call `Box.mk(3)` from
{{ref sec:implicit-functor-instantiation}} uses; `BoxTag.S` and `Box[Int]` are the same type.
`Box.mk(true)` uses a different instance, `Box[Bool]`. An alias of a module names the same
instance as the module. Two distinct argument modules, on the other hand, give distinct
instances even if both implement their interface for the same type: for two modules `A` and
`B` that both implement `Library.Type` with `rep type T = Int`, `Box[A]` and `Box[B]` are
different instances with different types.

Applicativity also covers applications written inside a functor's body. In
[`inference.rav`](./inference.rav), the functor `G[E: Library.Type]` has a member
`flag(b: Box[E])`, whose parameter type applies `Box` to `G`'s own parameter `E`. In the
instance `module GI = G[Int]`, this application becomes `Box[Int]`, and it denotes the same
instance as `Box[Int]` written anywhere else. A value `b` of type `Box[Int]` can therefore be
passed to `GI.flag`. The call `G.flag(b)` works too, without `GI`: since `E` occurs in the
parameter type `Box[E]`, Raven infers `E := Int` from `b`'s type and uses the instance
`G[Int]`.

A call's instance can thus come from an instance that its argument types or its expected
result type already name. `Box.get(b)` takes the instance from the type of `b`, and
`val tag: BoxTag.S := Box.mkTag()` takes `Box[Int]` from the declared type. If two arguments
name different instances for the same parameter, such as values of `Box[A]` and `Box[B]` above,
the call is rejected: inference never treats the two types as one. To give every application
of a functor its own instance instead, use a unit-parameter factory, described next.

When a call does not determine its instance, call the member through a named instance, as in
`BoxTag.mkTag()`. Do the same for constructors and other members whose inference is more
limited than that of ordinary function calls.

## Generative factories {#sec:module-generative-factories}

A functor with a unit parameter, written `()`, is a factory: each application creates a new
instance, distinct from every other. In [`unit_factories.rav`](./unit_factories.rav), the factory
`Tokens` declares a nominal token type:

```raven
module Tokens() {
  type T = data { case token(value: Int) }
}
module First = Tokens()
module Second = Tokens()
module Alias = First
```

`First.T` and `Second.T` are distinct types. The alias `Alias` creates no new instance, so a
`First.T` value can also be used as an `Alias.T`. A type that the factory defines by an
equation, such as `type T = Int`, still equals `Int` in every instance, although the instances
are distinct.

An interface can also declare a unit parameter, for example `interface Factory() { type T }`.
A functor parameter `F: Factory` then stands for a factory that has not been applied yet: apply
it, as in `module Value = F()`, before using the members of its result. Inference never applies
a factory. A functor with named parameters can define a nested factory for its clients to apply.

A factory may apply other factories. A functor with named parameters may apply a factory only
if the factory's result, as far as its interface shows it, introduces no new nominal type,
field, predicate, invariant, or atomic-update procedure. Otherwise, two applications of the
functor to the same arguments would contain different fresh members, and the functor would not
be applicative. The check includes inherited and nested members, takes sealing into account, and
looks into module applications inside the result. The result may still contain aliases of
existing resources and instances of functors defined outside it, since those keep their
identities.

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

Such a result may contain ordinary procedures and lemmas. Values without a definition and
functions without a body are rejected, conservatively, because each application would introduce
new unconstrained logical symbols; results whose module structure is recursive are rejected
too. A factory passed as a parameter is checked through its declared interface: an abstract
type in that interface counts as new, even if the factory passed at a particular application
defines it by an equation. Functors nested in the result that are not applied there are checked
conservatively too, including the nominal declarations in their own results. This rule is
stricter than OCaml's, which restricts only fresh types, because Raven also has nominal
resources and atomic updates.

Factories are sealed like other modules: a factory declaration, an unapplied alias of a factory,
or an individual application can each be sealed, as described below.

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

{{ref sec:sealing}} introduces sealed functors: every instance shows only the functor's
interface, whether the instance is declared, inferred from a call, or written in a type. The
functor's own body still sees its representation. A sealing declaration names exactly one
interface.

A module without parameters can be sealed the same way. Outside its own body, `module M :> I {
... }` shows only the members of `I`, and its abstract types are distinct from every other type.
You can also seal an existing module, or a single instance of a functor, after the fact:
`module V :> I = N` makes `V` a view of the module `N` through the interface `I`, and
`module V :> Stack = F[Int]` makes `V` a view of the instance `F[Int]` through `Stack`. The
module `N`, or the functor `F`, has to declare that it implements the interface, and Raven takes
the interface's arguments, such as `Stack`'s element type, from that declaration. Code that names
`N` directly still sees its definitions, but through `V`, the type `V.T` is abstract and distinct
from `N.T`.

### Sealing unapplied functors

An unapplied functor can also be given a sealed view, as checked in
[`functor_aliases.rav`](./functor_aliases.rav):

```raven
module Hidden :> Box = Implementation
module First = Hidden[Int]
module Second = Hidden[Int]
module Alias = Hidden
```

The functor `Implementation` must declare that it implements `Box`. `Hidden` takes the same
parameters as `Implementation`, in the same order and with the same constraints. Each instance
of `Hidden` shows `Box`, with the arguments that `Implementation`'s declaration gives `Box`: if
`Implementation[X, Y]` implements `Box[Y]`, then `Hidden[Int, Bool]` shows `Box[Bool]`. The
interface can also have no parameters, or be an alias of an already applied interface.

Applications of `Hidden` or `Alias` to the same arguments have the same abstract types: in the
example, `First` and `Second` have the same type `T`. These types are distinct from
`Implementation[Int]`'s and from those of any other sealed view of `Implementation`. Type
equations stated in the interface itself remain visible. If the sealed functor is a factory,
its views are applied with `()` too, and each application, also through an alias, creates a
new instance. A sealed view of a functor can be passed for a functor parameter whose interface it
declares. Raven then also checks that the two agree on the constraints of their parameters and
on how results depend on parameters: a functor that returns `Box[Int]` for every argument
cannot stand for one that returns `Box[E]` for its argument `E`.

The implementation remains available through its own name, with its representation and any
members beyond the interface. Creating a view does not verify its body a second time. The target
of a view can also be an interface instead of an implementation; its members are then assumed
without proof, as when an interface is instantiated directly, which models an API whose
implementation is not available.

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

This example is checked in [`checked_views.rav`](./checked_views.rav). `Client[Counter]` is still
rejected, because `Counter` does not declare that it implements `Positive`; creating `View` does
not add that declaration to `Counter`. If the target already declares that it implements the
requested interface, Raven checks the view like any module argument and generates no forwarding
code, so the view's members are the target's members.

Otherwise, Raven generates functions, procedures, and lemmas that forward to the target's
members, and verifies them against the interface like any other code. Logically atomic
procedures forward through an atomic update, including its abort-restoration obligations.
Physically atomic requirements must be satisfied by physically atomic target procedures. The
adapter does not coerce atomic update tokens between different procedures.

The view's types, fields, predicates, and invariants are aliases of the target's, so they are
the same types and resources. A predicate or invariant alias can also be written explicitly, as
`pred p(x: Ref) = Actual.p` or `inv shared(x: Ref) = Actual.shared`; its signature and parameter
modes must match those of the target. The constraints of a field in the interface and in the
target must be equivalent. Writing `module View :> Positive = checked Counter`
adds ordinary sealing, so clients see the interface's abstract representation.

The target must be the name of a module: to adapt a functor application, bind it to a name
first, then adapt that name. The interface can have parameters and abstract nested module
members. Raven does not yet generate forwarding code for data types or for values and callables
that the interface defines, for nested modules that it defines concretely, for contract clauses
added by extensions, or for public signatures that expose atomic-update tokens; adapt those
members explicitly. These restrictions do not apply when the target already declares that it
implements the interface.
