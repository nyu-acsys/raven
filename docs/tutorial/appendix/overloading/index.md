# Function and Operator Overloading

*Assumes: {{ref sec:func-vs-proc}} and {{ref sec:import}}.*

A function name can have several definitions with different parameter types. Raven chooses a
definition from the types of its arguments. Operators use the same rules: `s ++ t` is a
function call whose name is `++`, written with infix notation.

The examples in [`functions.rav`](./functions.rav) and
[`operators.rav`](./operators.rav), and [`literals.rav`](./literals.rav) are complete,
checked programs.

## Choosing a definition {#sec:overload-resolution}

These two functions can share a name because their parameter types differ:

```raven
module Measures {
  inline func measure(x: Int) returns (r: Int) { x }
  inline func measure(x: Bool) returns (r: Int) { x ? 1 : 0 }
}
```

After `import Measures._`, `measure(3)` returns `3`, while `measure(true)` returns `1`.
The definition selected for a call must accept its arguments, including the usual ghost and
implicit-parameter checks. If several definitions apply, Raven chooses the unique one with
more specific parameter types. For example, an `Int` parameter is more specific than a `Real`
parameter for an integer argument. Return types do not rank definitions, and two functions
cannot be distinguished only by their return types.

An ambiguous call is an error. Qualify the function name to choose a module, or annotate an
argument to make its type explicit. Empty collections often need this extra context; write
`([||] : Seq[Int])`, for example, when the surrounding call does not determine the sequence's
element type. Generic library functions use the same resolution and infer their module
instances as described in {{ref sec:implicit-functor-instantiation}}.

## Imports and shadowing {#sec:overload-imports}

Imports of functions with the same name combine their definitions:

```raven
module IntegerMeasure {
  inline func measure(x: Int) returns (r: Int) { x + 1 }
}

module BooleanMeasure {
  inline func measure(x: Bool) returns (r: Int) { x ? 2 : 0 }
}

module ImportedClient {
  import IntegerMeasure.measure
  import BooleanMeasure.measure

  lemma examples() {
    assert measure(3) == 4;
    assert measure(true) == 2;
  }
}
```

A local declaration takes precedence over imported definitions, and a nearer lexical binding
hides the entire outer group of definitions. Raven does not search the hidden group when the
nearer binding has no applicable signature. A qualified call such as
`Measures.measure(true)` restricts lookup to that module and still resolves any overloads
within it. Local and bound variables have a single binding; they are not overloaded.

## Symbolic infix functions {#sec:overload-symbols}

A symbolic name such as `+?` can be declared with `func` and used infix:

```raven
module Symbols {
  inline func +?(x: Int, y: Int) returns (r: Int) { 10 * x + y }
  inline func +:(x: Int, y: Int) returns (r: Int) { 10 * x + y }
}
```

After `import Symbols._`, `1 +? 2` is the call `Symbols.+?(1, 2)`.
An operator's spelling determines its precedence and associativity; a declaration cannot
change them. For names that do not end in `:`, the first character chooses the precedence
class, from highest to lowest:

| First character | Precedence class |
|---|---|
| `*`, `%` | multiplication |
| `+`, `-` | addition |
| `<`, `>` | comparison |
| `=`, `!` | equality |
| `&` | conjunction |
| `\|` | disjunction |

These infix functions associate to the left, except that comparisons form chains:
`a <+> b <+> c` means `(a <+> b) && (b <+> c)`. Thus `1 +? 2 * 3` evaluates to `16`,
and `1 +? 2 +? 3` evaluates to `123`.

Names ending in `:` associate to the right, regardless of their first character, and bind
between addition and comparison. The example `1 +: 2 +: 3` means `1 +: (2 +: 3)` and evaluates
to `33`. The list constructor `::` uses this same notation. Reserved spellings such as `+`
retain their existing meaning; the next section describes the fixed spellings Raven makes
available as function names.

## Fixed operator notation {#sec:overload-operators}

Alongside symbolic infix functions, Raven supports the fixed operator spellings below.
Declare them with `func`, just like an ordinary function; no separate syntax declaration is
needed.

| Expression | Equivalent call |
|---|---|
| `s ++ t` | `++(s, t)` |
| `s ** t` | `**(s, t)` |
| `s -- t` | `--(s, t)` |
| `s subseteq t` | `subseteq(s, t)` |
| `choose(s)` | `choose(s)` |
| `e in s` | `in(e, s)` |
| `e !in s` | `!(in(e, s))` |
| `x < y` | `<(x, y)` |
| `x <= y` | `<=(x, y)` |

Membership has an element-first signature. `!in` negates the same `in` call; it does not have
its own definition. Explicit calls and infix expressions select definitions in the same way.
Qualified calls such as `Numbers.++(1, 2)` are useful when several modules provide an operator.

For example, this module defines integer addition with the `++` spelling:

```raven
module Numbers {
  inline func ++(x: Int, y: Int) returns (r: Int) { x + y }

  inline func _[_.._](s: Int, lo: Int, hi: Int) returns (r: Int) {
    s + lo + hi
  }
}
```

After `import Numbers.++`, `1 ++ 2` calls `Numbers.++(1, 2)` and returns `3`.
The range definition will be used below. Its arithmetic meaning is chosen by this module;
operator notation alone does not prescribe a meaning.

The standard prelude imports set operations from `Library.Sets`, sequence operations from
`Library.Seq`, and list membership and concatenation from `Library.List`. The same declaration
and import rules apply to these names. With `--nostdlib`, define the functions in your own
modules and import them yourself.

`<` and `<=` also have built-in numeric definitions, available with or without the standard
library. They compare `Int` or `Real` operands and return `Bool`; an imported definition with
more specific parameter types can take precedence. `Library.OrderedType` declares `<` for its
ordered values and defines `<=` from `<` and equality. An implementation can supply its order directly:

```raven
module Keys: Library.OrderedType {
  rep type T = data { case key(value: Int) }

  func <(x: T, y: T) returns (r: Bool) { x.value < y.value }
}
```

After `import Keys._`, comparisons between keys select `Keys.<` and `Keys.<=`, while numeric
comparisons still select their built-in definitions. Arithmetic, equality, logical connectives,
`>` and `>=` remain intrinsic operations.

## Index, range, and update patterns {#sec:overload-patterns}

The index, range, and update spellings combine a function name with brackets and holes for
operands:

| Expression | Function name and call |
|---|---|
| `s[i]` | `_[_](s, i)` |
| `s[lo..hi]` | `_[_.._](s, lo, hi)` |
| `s[..hi]` | `_[.._](s, hi)` |
| `s[lo..]` | `_[_..](s, lo)` |
| `s[i := e]` | `_[_:=_](s, i, e)` |

A declaration's holes correspond to its explicit parameters, in order. Whitespace within the
pattern is ignored. These patterns require two, three, two, two, and three explicit parameters,
respectively; implicit ghost parameters may follow them. Import and qualify the whole pattern,
as in `import Numbers._[_.._]` or `Numbers._[_.._](10, 1, 3)`. With that import,
`10[1..3]` calls the range function above and returns `14`.

An update operator must return the same type as its first, container parameter. This lets
indexed assignments use the same function: `s[i] := e` means `s := s[i := e]`.
Nested assignments compose updates; `s[i][j] := e` means `s := s[i := s[i][j := e]]`.
Here is a custom container with one entry, at index zero:

```raven
module SingleEntry {
  rep type T = data { case entry(value: Int) }

  inline func _[_](s: T, i: Int) returns (r: Int) {
    i == 0 ? s.value : 0
  }

  inline func _[_:=_](s: T, i: Int, e: Int) returns (r: T) {
    i == 0 ? entry(e) : s
  }
}
```

After `import SingleEntry._`, `entry(1)[0]` calls the index function and returns `1`;
`entry(1)[0 := 2]` calls the update function and returns `entry(2)`.
The assignment `s[0] := 2` assigns the updated container back to `s`.
Both bracket expressions can also be called explicitly, as in `SingleEntry._[_](s, 0)`
and `SingleEntry._[_:=_](s, 0, 2)`.

Maps have built-in polymorphic definitions with signatures `(Map[K, V], K) -> V` for
indexing and `(Map[K, V], K, V) -> Map[K, V]` for updates. The map's domain and range determine
the types expected for the index and replacement value, which may have more specific types.
Both `m[i]` and `_[_](m, i)` select the index definition, and both `m[i := e]` and
`_[_:=_](m, i, e)` select the update definition, when no more specific applicable definition
wins.

The prelude imports sequence index and update definitions, which call `Seq.index` and
`Seq.update`. These bracket expressions use ordinary function resolution, as do the
enumeration literals described below.
For sequences, `s[..hi]` calls `take(s, hi)`, `s[lo..]` calls `drop(s, lo)`, and
`s[lo..hi]` calls `drop(take(s, hi), lo)`. Set overloads preserve finite results for unions of
finite sets, intersections with a finite set, and differences from a finite set. See
{{ref app:stdlib-types}} for the library's collection operations.

Heap arrays use the statement access rules from {{ref sec:stdlib-array}}. Their indexed writes
update heap cells, and functional expressions such as `a[i := e]` remain unavailable for them.

## Enumeration literals {#sec:overload-literals}

Enumeration notation uses an empty function, a singleton function, and `++` to combine
elements. The prelude supplies these definitions for sequences, lists, and finite sets:

| Collection | Empty | Singleton | Several elements |
|---|---|---|---|
| Sequence | `[||]` | `[|1|]` | `[|1, 2|]` |
| List | `<||>` | `<|1|>` | `<|1, 2|>` |
| Finite set | `{||}` | `{|1|}` | `{|1, 2|}` |

For example, `[|1, 2|]` combines `[|_|](1)` and `[|_|](2)` with `++`.
Longer literals associate to the right: `[|1, 2, 3|]` means
`[|_|](1) ++ ([|_|](2) ++ [|_|](3))`, even if `++` is not associative.
The function `[||]()` supplies the empty sequence. A type annotation provides the element
type for an empty collection: `val xs: List[Int] := <||>;`. Context also reaches nested
elements, so `val ss: Seq[Seq[Int]] := [|[||]|];` determines both sequence types.

You can choose another matching run of brackets for your own enumeration notation.
The opening and closing brackets must be contiguous and surround the `|` markers.
Opening symbols may be `(`, `[`, `{`, or `<`; closing symbols reverse and match them.
In expression positions, `([|1|])` uses the compound delimiter `([`. To group a
sequence literal with parentheses, insert whitespace: `( [|1|] )`. Brackets that
start an indexed access and braces that start a body keep those roles.
Declare the matching empty and singleton patterns, then import them together with your
combining function:

```raven
module SumLiteral {
  inline func {{||}}() returns (r: Int) { 0 }
  inline func {{|_|}}(e: Int) returns (r: Int) { e }
  inline func ++(x: Int, y: Int) returns (r: Int) { x + y }
}
```

After `import SumLiteral._`, <code v-pre>{{||}}</code> is `0` and
<code v-pre>{{|1, 2, 3|}}</code> is `6`.
These patterns can also be called explicitly, as in
<code v-pre>SumLiteral.{{|_|}}(1)</code>.
The declarations determine the result type and meaning of the literal.
Set comprehensions such as `{| x: Int :: x > 0 |}` retain their binder syntax.
The finite-set constructors wrap the native `finset()` and `finset(e)` primitives,
which construct the empty set and a singleton while preserving their `FinSet` type
and direct SMT encoding. Enumeration syntax itself uses ordinary library calls.
