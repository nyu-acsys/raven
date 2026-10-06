# 1. Sequential Raven

This part restricts itself to the *sequential* fragment of Raven: values, pure and imperative
computation, control flow, recursion, and data types. There is no heap, no ownership, and no
threads yet. Those start in [Part 2](../ownership/). If you've used an *auto-active* verification
tool before (one where you write specifications up front and the tool checks them automatically,
without further interaction), most of this will feel familiar, and that's intentional. The places
where this part *does* diverge from that familiar ground are flagged explicitly, because Part 2
onward builds on them.

To give later forward references some context, here's the overall plan. Across Parts 1–4, a
single running example, a hit counter, grows from a plain value (this part), to a heap-allocated
object (Part 2), to an interface with more than one implementation (Part 3, including a
*saturating* variant that stops counting at a cap instead of overflowing), to something safely
touched by multiple threads at once (Part 4). Nothing below depends on that future context to
make sense, but a couple of examples prepare the ground for it.

All code below is in [`hit_counter_pure.rav`](./hit_counter_pure.rav). Open it side by side
with this text. Every listing here should verify as-is.

## Values and types {#sec:values-and-types}

Raven's basic types are `Int`, `Bool`, `Real`, `Ref` (heap references, covered in Part 2),
tuples, `Set[T]`, and `Map[K, V]`. There's no separate `Unit` type. The unit value and its type
are both written `()`, the empty tuple, which is a special case of tuples rather than its own
category.

The type `Real` represents actual *real numbers* and is meant to be used only in specifications.
It has "infinite" precision and is not to be confused with floating point numbers.

`Set` and `Map` are already *generic* types (`Set[T]` for any `T`). Part 3's module system is
what lets you define your own generic-*seeming* types the same way, by parameterizing a module
over another module standing in for the element type. `Set` and `Map` aren't special-cased
language magic. They are simply predefined.

All members of Raven types, including `Set` and `Map`, are *values*, not containers you mutate in
place. For example, `recordVisitor` below builds a new set rather than modifying `seen`:

```raven
func recordVisitor(seen: Set[Int], id: Int) returns (r: Set[Int])
  ensures forall x: Int :: (x in r) == (x in seen || x == id)
{
  seen ++ {|id|}
}
```

`{|id|}` is a singleton-set literal, `++` is set union, and `in` is membership. Set/map
*comprehensions* (`{| k: Int :: k > 5 |}`) show up later once we need to describe unbounded
families of values at once.

A comprehension like that one can describe an infinite set, so `Set[T]` on its own doesn't
promise finiteness. `FinSet[T]` is a built-in subtype of `Set[T]` for sets that are finite by
construction. Union, intersection, difference, and enumeration literals (including `{|id|}`
above) all produce a `FinSet[T]` whenever their inputs are finite sets. In fact, `recordVisitor`
above could equally well have been typed `FinSet[Int] -> FinSet[Int]`. However, there's no way to
*downcast* a plain `Set[T]` into a `FinSet[T]`, even one you happen to know is finite, because the
guarantee is purely syntactic. `choose(s)`, usable on either `Set[T]` or `FinSet[T]`, picks some
element out of a nonempty `s`. It returns the same element every time you write `choose(s)` for
the same `s`, so it's safe to reason about across multiple uses. You'll need both once a
termination measure has to shrink a set one element at a time ({{ref sec:well-founded-order}}).

## Functions (`func`) vs. procedures (`proc`) {#sec:func-vs-proc}

```raven
func next(c: Int) returns (r: Int)
  ensures r == c + 1
{
  c + 1
}

proc bump(c: Int) returns (r: Int)
  requires c >= 0
  ensures r == c + 1
{
  r := c + 1
}
```

Observe that `next` and `bump` have the same contract, but they are two different callable
kinds. A `func` defines a mathematical function over values. Its body is a single expression,
not a statement block. Crucially, **a `func` must actually terminate on every input**. The
purpose of a `func` is to denote a value, and the tool's soundness depends on that value
existing. However, Raven doesn't *check* this by default. A recursive `func`'s termination is
silently *assumed* unless you give it a `decreases` clause, which causes it to be checked
instead. ({{ref sec:control-flow}} below covers this properly. In short, it's good practice to
add `decreases` to every recursive `func` you write rather than relying on the default
assumption.) A `proc`, by contrast, doesn't need to terminate at all. Nothing later in a proof
relies on a `proc` to denote a value the way a `func` does, so a `proc` that loops or recurses
forever on some input just means the proof establishes nothing about that input. It does not
make anything unsound. That said, you can add a `decreases` clause to a `proc` contract if you
want to prove that it terminates.

This difference is the main reason for the split between the two callable kinds. You can use a
`func` **both inside and outside a specification** (a `requires`/`ensures`/`invariant`). A `proc`
can only be used in code, never inside a spec. Predicates and shared invariants (Part 2 onward)
are the opposite case: they can appear inside specs, but never in ordinary code. Keep this
three-way split in mind, as it resurfaces as the *concrete*-vs-*ghost* statement distinction once
Part 4 introduces ghost code.

Another asymmetry is important to understand early on: **`func`s cannot have a `requires`
clause**. Their contracts must be total, defined for every input of the argument types. A `proc`
doesn't have this restriction. You can try this out with
[`broken/half_requires.rav`](./broken/half_requires.rav):

```raven
func half(n: Int) returns (r: Int)
  requires n % 2 == 0
  ensures 2 * r == n
{
  n / 2
}
```

This is rejected outright, before any proof obligation is even generated: `[Type Error] half may
not have a requires clause; func/pred/invariant contracts must be total.` Some pure operations
are naturally partial. Here, `half` only really makes sense for even `n`. To work around the
restriction, state that constraint as a guarded fact in the postcondition instead of a
precondition ([`broken/half_total.rav`](./broken/half_total.rav)):

```raven
func half(n: Int) returns (r: Int)
  ensures n % 2 == 0 ==> 2 * r == n
{
  n / 2
}
```

This one verifies. `half` is now total: it's defined, and proved to return *something*, for
every `Int`, including inputs Raven can't make any interesting claim about. The guard means
nobody relying on `half`'s postcondition for an odd input gets to conclude anything false. `next`
above never needed a guard like this. Unlike `half`, its postcondition (`r == c + 1`) holds for
every `Int`, negative or not, so there was no partial fact to guard against.

## Contracts on pure code {#sec:contracts-pure-code}

The `requires`/`ensures` clauses we have seen so far are exactly the pre- and post-conditions of
Hoare triples in classical Hoare logic. A precondition must hold at the call, and a
postcondition is guaranteed on return. No heap is involved yet, so a verification condition (VC)
at this point is just a question of whether one boolean formula follows from another. Try
changing `next`'s postcondition to `r == c + 2` and re-verify to watch a VC fail on purely
arithmetic grounds.

## Control flow: recursion and loops {#sec:control-flow}

```raven
func afterHits(c: Int, n: Int) returns (r: Int)
  ensures n >= 0 ==> r == c + n
  decreases n
{
  n <= 0 ? c : afterHits(next(c), n - 1)
}

proc bumpN(c: Int, n: Int) returns (r: Int)
  requires c >= 0 && n >= 0
  ensures r == c + n
{
  r := c
  var i := 0
  while (i < n)
    invariant 0 <= i <= n
    invariant r == c + i
  {
    r := r + 1
    i := i + 1
  }
}
```

(`0 <= i <= n` is a chained comparison. Raven accepts it directly as shorthand for `0 <= i && i
<= n`, which is how every other example in this tutorial spells it out. Both are fine, so use
whichever reads better to you.)

`bumpN` is also this file's first use of `var`, which declares a *mutable* local variable. The
assignment `i := i + 1` a few lines down is only legal because `i` was declared with `var`.
Raven has a second local-declaration form, `val`, for a binding you intend to set once and never
change. You'll see it starting in Part 2, in patterns like `val x := c.count` for a one-time
heap read. The difference is more than documentation, because Raven checks it: reassigning a
`val` is a `[Type Error] Cannot assign to value x`, not a warning. Prefer `val` when nothing
later needs to change the binding. It signals to both the reader and the tool that this value is
fixed for the rest of its scope.

`afterHits` proves the same fact as `bumpN`, recursively. The clause `decreases n` is what lets
Raven accept the recursion as terminating. Without a `decreases` clause, Raven doesn't refuse to
verify the function. It just silently *assumes* termination rather than checking it. (There's a
stricter mode that checks this instead of assuming it, but as of this writing it's a
command-line-only flag that isn't exposed in the VS Code extension. It's worth knowing the
assumption is there, even though you can't change it from the editor today.) `bumpN` proves the
same fact iteratively, and this is the one place in this file where the proof burden is on you
rather than on Raven's automation. A `while` loop needs an explicit `invariant`: a fact that's
true before the loop and after every iteration, and that is strong enough to imply the
postcondition when combined with the loop's exit condition. Try deleting `invariant r == c + i`
and re-verifying. You'll get "This loop invariant may not be maintained," because `0 <= i <= n`
alone says nothing about what `r` actually is.

## A more interesting termination measure {#sec:termination-measure}

The termination measure `n` in the clause `decreases n` above is a single `Int` counting down
to 0. This is a common case, but not the only shape a termination argument can
take. [`termination.rav`](./termination.rav) has Ackermann's function, the textbook example
illustrating why:

```raven
func ackermann(m: Int, n: Int) returns (r: Int)
  decreases m, n
{
  m <= 0 ?
    n + 1 :
    (n <= 0 ? ackermann(m - 1, 1) : ackermann(m - 1, ackermann(m, n - 1)))
}
```

`decreases m, n` is a **lexicographic** measure. Raven orders the pair the way a dictionary
orders words. A recursive call is fine if `m` strictly decreases (whatever happens to `n`), or
if `m` stays exactly the same and `n` strictly decreases. No *single* `Int` can play this role
here. The innermost call, `ackermann(m, n - 1)`, leaves `m` untouched and only decreases `n`. It's
the call *around* it, `ackermann(m - 1, ...)`, that brings `m` down, regardless of what
`ackermann(m, n - 1)` returns. Try
[`broken/ackermann_single_measure.rav`](./broken/ackermann_single_measure.rav), which is the same
function with just `decreases m`. It fails exactly on that inner call, with `This
decreases clause's termination measure may not decrease on this recursive call`. Indeed, `m`
doesn't decrease there, only `n` does, and a single-`Int` measure has no way to express "or the
other component decreased instead."

A comma-separated `decreases` clause works for any number of components, compared
lexicographically from left to right. Each component's type just needs *some* well-founded order
that Raven knows about. This can be a built-in one like that of `Int` (bounded below by 0, which
is what `decreases n` relies on), or one you define yourself. Part 3 comes back to that second
option, once the necessary module system features have been introduced.

## Algebraic data types {#sec:algebraic-data-types}

```raven
type Outcome = data {
  case ok(value: Int)
  case capped
}

func boundedNext(c: Int, cap: Int) returns (r: Outcome)
  ensures c >= cap ==> r == capped
  ensures c < cap ==> r == ok(c + 1)
{
  c >= cap ? capped : ok(c + 1)
}
```

The keyword `data` declares an *algebraic data type* (ADT, or sum type). Here, `Outcome` is
either `ok(value)` or `capped`. A nullary case like `capped` can optionally take a trailing `()`
at construction sites (`capped()`). This example anticipates the "saturating implementation"
mentioned at the start of this part. Part 3 gives `Counter` a second implementation, built around
exactly this idea, that stops counting at a cap instead of overflowing. `Outcome` (or a type just
like it) is what its `create`/`increment` operations will return there.

So far, `Outcome` values have only been *constructed*. Two constructs take such ADT values apart
again.

The first is the infix operator `is`: `r is ok` is a `Bool` saying which constructor `r` was
built with. It pairs with destructors. `r.value` reads the argument of a value built with
constructor `ok`, which is only meaningful when `r` really *is* an `ok` value, so the two
usually appear together:

```raven
ensures r is ok ==> v == r.value
```

`is` binds exactly like `==`, so it sits inside a larger formula without needing parentheses.
Both `r is ok && v > 0` and `r is ok ==> ...` group the way you'd expect.

Technically, the `is` predicate is syntactic sugar: `r is ok` is equivalent to the equality `r
== ok(r.value)`. For a case with no arguments the two are interchangeable. `r is capped` and
the `r == capped` used by `boundedNext` above say exactly the same thing. The `is` operator is
most useful for cases where the constructor *does* carry arguments, since the equality you'd
otherwise write has to reconstruct the value field by field.

Writing a whole case analysis using the `is` operator and destructors gets tedious, though.
Inside a function body you would typically use *pattern matching* instead. The `match` construct
picks the case *and* names its arguments in one step:

```raven
func settle(r: Outcome, fallback: Int) returns (v: Int)
  ensures r is ok ==> v == r.value
  ensures r is capped ==> v == fallback
{
  match r {
    case ok(n) => n
    case capped => fallback
  }
}
```

Each arm of `match` names a case and binds one variable per argument. Above, `n` is the `Int`
inside an `ok`, and it is in scope only for that arm's body. A nullary case binds nothing and
takes no parentheses, hence the bare `case capped =>`. A `match` is an ordinary expression, so
every arm has to produce the same type, here the `Int` this `func` returns.

Raven checks that the arms are **exhaustive**. You must name every case exactly once, or end
with a catch-all `case _ =>` arm covering whatever is left. Forgetting one is a type error rather
than a silent gap that only shows up later as a failed proof. You can also write `_` in place of
an argument name when you don't need it (`case ok(_) => 0`).

The `is` operator remains useful in places where an exhaustive `match` is not needed.

Naming an arm's pattern variable after the field it binds is fine, and often clearest.
`case ok(value) => ...` does not stop a later `r.value` from resolving. The `f` in `r.f` is a
destructor name looked up in `r`'s own type, not a reference to whatever `f` happens to mean
nearby, so it never collides with a variable of the same name.

## Quantifiers, briefly {#sec:quantifiers}

The function `recordVisitor` above already used a `forall` quantifier. There are two things
worth knowing now. Part 5 revisits both in more depth in the resource-owning setting.

- **The direction in which you use a quantifier matters.** *Proving* a `forall` (e.g. in an
  `ensures` clause) is generally robust, while *assuming* one (e.g. in a `requires` clause) is
  generally not. (Loop invariants act as both `ensures` and `requires` clauses at the same
  time.) For `exists` it's the mirror image: *assuming* one is robust, while *proving* one can be
  finicky. So if you need to *prove* that "some property holds of at least one element," see if
  it can be phrased as an upper/lower bound (a `forall`) instead. [Exercise 3](#exercises) below
  is built around exactly this choice. None of this is a hard rule, just a good default to try
  first. Used carelessly, quantifiers of either kind can degrade verifier performance or cause
  outright timeouts, a topic Part 5 comes back to.
- **Triggers.** The curly braces in a quantifier, right after the bound variables, are a hint
  telling the underlying SMT solver *which* terms should cause it to instantiate the
  quantifier (a technique called E-matching). Here is the full syntax, taken from
  [Exercise 3](#exercises)'s solution:

  ```raven
  ensures forall j: Int :: {counts[j]} 0 <= j && j < len ==> counts[j] <= r
  ```

  `j` is the bound variable, `{counts[j]}` is the trigger, and `0 <= j && j < len ==> counts[j]
  <= r` is the body. The SMT solver will consider instantiating this `forall` at a specific
  value of `j` whenever the term `counts[j]` (for that same value) shows up elsewhere in the
  proof. You'll see triggers wherever a `forall` ranges over something indexed, like a
  `Map`. You don't need to fully understand triggers yet. Just recognize the curly-brace syntax
  and know that it's there to help the SMT solver, not to change what the formula means.

## Why this matters for concurrency

Nothing in this chapter is concurrency-specific, and that is intended. Everything here is
standard Hoare logic over plain values, and if you've used an auto-active verification tool
before, none of it should have surprised you. Part 2 is where Raven's reasoning starts to diverge
from that familiar ground. The concepts it introduces (ownership, fractional permissions, the
separating conjunction) are exactly the machinery that makes concurrent reasoning possible later.
Everything covered so far will be used again, even though nothing specific to Raven has happened
yet.

## Debugging Corner

Raven distinguishes "doesn't type-check" from "doesn't verify" via the diagnostic's bracketed
kind prefix. It's worth deliberately triggering both once if you haven't already (Part 0 showed
one of each). For a loop invariant, Raven also tells you *which* half failed:

- **"This loop invariant may not hold upon loop entry"**: your invariant is wrong even before
  the loop starts running (often because you forgot to account for the loop's initialization
  code).
- **"This loop invariant may not be maintained"**: it holds going in, but running the loop body
  once breaks it (often because the invariant is too weak to survive a single iteration).

These are two different bugs with two different fixes, and the message tells you which one
you're looking at.

## Exercises

Each exercise lives in `exercises/` as a stub with a deliberately incomplete
loop invariant (`invariant true // TODO`). Fill it in until "Raven: Verify File" turns green.
Checked solutions are in `solutions/` if you get stuck or want to compare your answer.

1. **[`sum_range.rav`](./exercises/sum_range.rav)**: sum of `1 + 2 + ... + n`.
2. **[`gcd.rav`](./exercises/gcd.rav)**: gcd via repeated subtraction.
3. **[`hot_day.rav`](./exercises/hot_day.rav)**: the busiest day in a per-day hit log. This
   exercise is designed to reward the `forall`-over-`exists` preference from
   {{ref sec:quantifiers}} above when proving rather than assuming a quantified fact.

## What's next

[Part 2](../ownership/) puts this same counter on the heap, with one `field` and one `Ref`, and
asks what it means to own a piece of mutable state.
