# Advanced Module Features

*Assumes: Part 3's interfaces, functors, and {{ref sec:implicit-functor-instantiation}}.*

The module chapter introduces the common forms. This appendix covers the additional inference
rules, type identities, generative factories, and sealing forms that matter when building
reusable libraries, and how Raven keeps invariant masks sound across module boundaries.

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

## Invariant masks across module boundaries {#sec:module-namespace-contracts}

*Also assumes: {{ref sec:shared-invariants}}.*

Within a single program, Raven checks masks precisely: it knows the body of every invariant a
callable might open, and checks with the solver that two instances open at the same time are
distinct. Modules break that view. A callable is verified once, against an interface whose
invariants and predicates may be abstract, but it must be sound for every implementation of
that interface, including implementations written later. Raven therefore summarizes each
module's use of invariants in a *namespace contract*: the invariants it declares, the mask each
of its callables requires and grants, and the separation its generic code assumes from its
parameters. Raven infers these contracts, so you don't write them, and fixes each one when its
module is declared. Instances, sealed views and checked views carry their module's contract, and
every implementation and module argument is checked against the contract it is meant to
satisfy. The contract prevents two kinds of unsoundness, each a way to open the same invariant
twice and so to duplicate the resources it protects.

**Implementations reaching back.** In
[`broken/namespace_reach_back.rav`](./broken/namespace_reach_back.rav), the interface
`Resource` declares an abstract invariant `shared` and a lemma `touch` that requires it. From the
interface, `touch`'s mask is just `shared`. The implementation `Actual` defines `shared` to
contain another invariant, `cell(root)`, and its `touch` opens both:

```raven
module Actual : Resource {
  inv shared(x: Ref) { cell(root) }
  lemma touch(x: Ref) {
    unfold shared(x);
    unfold cell(root);
    fold cell(root);
    fold shared(x);
  }
}
```

A client that has `cell(root)` open can call `touch`, since `cell` isn't in `touch`'s mask. If
`touch` could then open `cell(root)` a second time, the client would hold `root.value` twice.
So an implementation keeps its interface's masks, and `unfold cell(root)` is rejected with
`[Verification Error] Invariant cell is not in the current mask`. The fix belongs in the
interface: it states which invariants `touch` may open, including the hidden ones. An `opens`
clause with a predicate entry asks for everything an implementation hides behind the
predicate's body, as in [`namespace_contracts.rav`](./namespace_contracts.rav):

```raven
interface Resource {
  inv shared(x: Ref)
  pred footprint(x: Ref) { shared(x) }
  lemma touch(x: Ref) requires shared(x) ensures shared(x) opens footprint(x)
}
```

Callers of `touch` now have to provide that whole footprint, which, for `Actual`, includes
`cell(root)`.

**Generic code assuming separation.** A functor's body is verified once for all of its
arguments. `Worker` in [`namespace_contracts.rav`](./namespace_contracts.rav) holds `cell(y)`
open while calling its parameter:

```raven
module Worker[P: Resource] {
  lemma work(x: Ref, y: Ref)
    requires cell(y) && P.shared(x)
    ensures cell(y) && P.shared(x)
    opens cell(y), P.footprint(x)
  {
    unfold cell(y);
    P.touch(x);
    fold cell(y);
  }
}
```

This is sound only if `P.touch` can't open `cell(y)`, which depends on `P`. Raven records the
assumption in `Worker`'s contract, as a requirement that `P`'s namespaces be disjoint from
`cell`'s, and checks it at every application. `Worker[Separate]`, whose `shared` contains no
invariants, is accepted. With `Actual`, `touch` opens `cell(root)`, so the two instances are
distinct only if `y != root`. Since `work` names both instances by formals that its body never
assigns, Raven checks this for the instances, as an assertion under `work`'s precondition.
Nothing there rules out `y == root`, so `Worker[Actual]`, in
[`broken/namespace_separation.rav`](./broken/namespace_separation.rav), is rejected at the
application with `[Verification Error] Cannot establish invariant namespace separation between
cell(y) and cell(root)`, with the call in `Worker` that made the assumption as a Related
Location. In [`namespace_instances.rav`](./namespace_instances.rav), the parameter's
`shared(x)` is `cell(x)`, and the generic lemma requires `x != y`, so the application verifies.
In the same way, a module passed for a parameter must satisfy the parameter's
contract. In particular, a callable that the parameter's interface promises grants its caller a
mask, like a constructor that allocates an invariant, must grant at least that mask. Otherwise
the application is rejected with `Incompatible module namespace contracts`.

**Limitations.** Contracts are conservative in three ways:

- Across a module boundary, instances are told apart only by the precondition of the generic
  callable, and only if they are named by formals that its body never assigns. Otherwise,
  separation is a property of invariant declarations. In
  [`broken/namespace_instances.rav`](./broken/namespace_instances.rav), the functor opens
  `cell(y)` through a local copy of `y`, so its application is rejected, although the same code
  verifies against the module directly. Applications inside other functors are always checked
  per declaration.
- Masks are fixed by the interface. An implementation can't open an invariant its interface's
  mask doesn't cover, even if no caller would ever have it open, unless it places the invariant
  inside a covered one, as in {{ref sec:invariant-regions}}. Declaring hidden invariants through a
  predicate entry instead makes every caller provide them, for every implementation.
- Holding an abstract resource doesn't, by default, let you open the invariants hidden in it;
  that permission has to be requested with a predicate entry, as above.

## Invariant regions {#sec:invariant-regions}

*Also assumes: {{ref sec:module-namespace-contracts}}.*

A predicate entry in an `opens` clause makes every caller provide what an implementation hides.
An implementation can instead place its private invariants inside a public one, which callers
provide anyway. In [`invariant_regions.rav`](./invariant_regions.rav), `Actual` declares that
`cell` lies within `shared`:

```raven
module Actual : Resource {
  inv shared(x: Ref) { cell(x) }
  inv cell(x: Ref) within shared(x) { exists v: Int :: own(x.value, v) }
  ...
}
```

An invariant instance now stands for a *region*: itself and its descendants. A mask that names
`shared(x)` covers `cell(x)` too, so `touch`, whose mask is `shared(x)`, may open both, and a
client of the sealed `Public` needs to know nothing about `cell`. In a module, a `within` clause
declares the invariant's parent: it names an invariant of the same module, and its arguments
must be parameters of the child, so each child instance has exactly one parent instance. The
child needs a definition, and ancestry can't be cyclic. An implementation may place its private
invariants anywhere, but not give a public invariant an ancestor its interface doesn't declare:
that is rejected with `Incompatible module namespace contracts: Realization gives invariant ...
an undeclared ancestor`.

Regions also decide which calls are safe while invariants are open. Opening an invariant doesn't
use up the mask. Instead, Raven records which instances are open, and a call requires that none
of them lies in the callee's region. A callee whose mask is `child(x)` may run while `root(x)` is
open, since `root(x)` isn't in that region. The converse is rejected: in
[`broken/region_reentry.rav`](./broken/region_reentry.rav), `reenter` calls `root_step`, whose
mask is `root(x)`, while `child(x)` is open, and gets `[Verification Error] Missing fold for
unfolded invariant child(x)`. Calling `root_step` before unfolding `child(x)` fixes it.

**Promising a region.** In an interface, a `within` clause promises that one invariant lies
within another:

```raven
interface Family {
  inv root(x: Int)
  inv leaf(x: Int, k: Int) within root(x)
}
```

A client may then open any `leaf(x, k)` under the mask `root(x)`, as `visit` does. Each
implementation keeps the promise through the parents it declares, possibly with private
invariants in between: `Tree` places `leaf` within a private `branch`, which lies within `root`.

**Bounding what an abstract resource depends on.** When you hold an abstract predicate or
invariant, Raven doesn't know which invariants its implementations put inside it, so it can't
tell them apart from the invariants you allocate or open. A `depends` clause bounds them:
`pred context(self: Ref) depends {}` promises that `context` depends on no invariant, and
`depends cell(x)` would allow the region of `cell(x)`. In the example, `fresh` holds
`Hidden.context(self)` and still allocates and opens a `counter` under `opens {}`. Without the
clause, it is rejected with `Cannot establish invariant namespace separation between counter
and dependencies(Hidden.context)`. Each implementation is checked against the bound, and one
whose definition depends on more is rejected with `the invariants context depends on exceed its
depends clause`. A bound only limits what a resource may depend on: it gives no permission to
open the invariants it names. Only predicates and invariants without a definition take a
`depends` clause.
