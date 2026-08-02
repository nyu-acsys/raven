# 1. Sequential Raven

This part restricts itself to the *sequential* fragment of Raven: values, pure and imperative
computation, control flow, recursion, and data types. No heap, no ownership, no threads yet —
those start in [Part 2](../02-ownership/). If you've used an *auto-active* verification tool
before (one where you write specifications up front and the tool checks them automatically,
without further interaction — Dafny and Viper are two well-known examples), most of this will
feel familiar; that's deliberate. Where this part *does* diverge from that familiar ground, it's
flagged explicitly, because those divergences are the seeds Part 2 onward will grow.

Here's the map, so later forward references land somewhere: across Parts 1–4, a single running
example — a hit counter — grows from a plain value (this part), to a heap-allocated object (Part
2), to an interface with more than one implementation (Part 3, including a *saturating* variant
that stops counting at a cap instead of overflowing), to something safely touched by multiple
threads at once (Part 4). Nothing below depends on that future context to make sense on its own
terms, but a couple of examples plant a seed for it, and it's easier to spot which ones if you
know the seed is coming.

All code below is in [`hit_counter_pure.rav`](./hit_counter_pure.rav) — open it side by side
with this text. Every listing here verifies as-is; if you change something and it stops
verifying, that's the point of a live editor, not a bug in the tutorial.

## 1. Values and types

Raven's basic types are `Int`, `Bool`, `Real`, `Ref` (heap references — Part 2), tuples,
`Set[T]`, and `Map[K, V]`. There's no separate `Unit` type — the unit value and its type are
both written `()`, the empty tuple; it's a special case of tuples, not its own category.

`Set` and `Map` are already *generic* types (`Set[T]` for any `T`), and — a forward pointer,
skip this if it doesn't land yet — Part 3's module system is what lets you define your own
generic-*seeming* types the same way, by parameterizing a module over another module standing in
for the element type. `Set`/`Map` aren't special-cased language magic; they just got there
first.

`Set` and `Map` are *values*, not containers you mutate in place — `recordVisitor` below builds
a new set rather than modifying `seen`:

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

## 2. Functions (`func`) vs. procedures (`proc`)

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
  r := c + 1;
}
```

Same contract, two different callable kinds. A `func` defines a mathematical function over
values — its body is a single expression, not a statement block. Crucially, **a `func` must
actually terminate on every input**: the entire point of a `func` is to denote a value, and the
tool's soundness depends on that value genuinely existing. In practice, though, Raven doesn't
*check* this by default — a recursive `func`'s termination is silently *assumed* unless you give
it a `decreases` clause, which is what actually gets it checked instead (§4 below covers this
properly; the short version is that it's good practice to add `decreases` to every recursive
`func` you write, rather than leaning on the default assumption). A `proc`, by contrast,
genuinely doesn't need to terminate at all, for a completely different reason: nothing later in
a proof is relying on a `proc` to denote a value the way a `func` does, so a `proc` that loops or
recurses forever on some input just means the proof establishes nothing about that input — not
that anything is unsound.

That last point is really the whole reason for the split: `func`, not `proc`, is the kind of
callable you can use **both inside and outside a specification** (a `requires`/`ensures`/
`invariant`) — predicates and invariants (Part 2 onward) can *also* appear inside specs, but only
there, never in ordinary code; a `proc` is the reverse, code-only, never inside a spec. Keep an
eye on this three-way split; it resurfaces as the *concrete*-vs-*ghost* statement distinction
once Part 4 introduces ghost code.

One asymmetry worth internalizing now: **`func`s cannot have a `requires` clause** — their
contracts must be total, defined for every input of the argument types, since a `func` might get
called from inside someone else's specification where there's no natural place to first
discharge a precondition. `proc`s don't have this restriction. Try it — it's
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
not have a requires clause; func/pred/invariant contracts must be total.` If a pure operation is
naturally partial — `half` only really makes sense for even `n` — state that constraint as a
guarded fact in the postcondition instead of a precondition
([`broken/half_total.rav`](./broken/half_total.rav)):

```raven
func half(n: Int) returns (r: Int)
  ensures n % 2 == 0 ==> 2 * r == n
{
  n / 2
}
```

This one verifies: `half` is now total (it's defined, and proved to return *something*, for
every `Int`, even inputs Raven can't make any interesting claim about), and the guard means
nobody relying on `half`'s postcondition for an odd input gets to conclude anything false. `next`
above never needed a guard like this in the first place — unlike `half`, its postcondition
(`r == c + 1`) genuinely holds for every `Int`, negative or not, so there was no partial fact to
guard against to begin with.

## 3. Contracts on pure code

`requires`/`ensures` here are exactly the Hoare triples you already know: a precondition that
must hold at the call, a postcondition guaranteed on return. No heap is involved yet, so a
verification condition (VC) at this point really is just "does this boolean formula follow from
that one" — nothing more exotic. Try changing `next`'s postcondition to `r == c + 2` and
re-verify to watch a VC fail on purely arithmetic grounds, no ownership involved at all.

## 4. Control flow: recursion and loops

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
  r := c;
  var i := 0;
  while (i < n)
    invariant 0 <= i <= n
    invariant r == c + i
  {
    r := r + 1;
    i := i + 1;
  }
}
```

(`0 <= i <= n` is a chained comparison — Raven accepts it directly as shorthand for `0 <= i && i
<= n`, which is how every other example in this tutorial spells it out; both are fine, use
whichever reads better to you.)

`bumpN` is also this file's first use of `var`, which declares a genuinely *mutable* local —
`i := i + 1;` a few lines down is only legal because `i` was declared with `var`. Raven has a
second local-declaration form, `val`, for a binding you intend to set once and never touch
again; you'll see it starting in Part 2, in patterns like `val x := c.count;` for a one-time
heap read. The difference isn't just documentation — Raven checks it: reassigning a `val` is a
`[Type Error] Cannot assign to value x`, not a warning. Prefer `val` when nothing later needs to
change the binding; it's a small signal, to a reader and to the tool alike, that this value is
fixed for the rest of its scope.

`afterHits` proves the same fact as `bumpN`, recursively; `decreases n` is what lets Raven accept
the recursion as terminating. Without a `decreases` clause, Raven doesn't refuse to verify the
function — it just *assumes* termination rather than checking it, silently. (There's a stricter
mode that checks this instead of assuming it, but as of this writing it's a command-line-only
flag, not yet exposed anywhere in the VS Code extension — worth knowing the assumption is there,
not something you can act on from the editor today.) `bumpN` proves the same fact iteratively,
and this is the one place in this file where the proof burden is on you rather than on Raven's
automation: a `while` loop needs an explicit `invariant`, a fact that's true before the loop,
after every iteration, and strong enough that, combined with the loop's exit condition, it
implies the postcondition. Try deleting `invariant r == c + i` and re-verifying — you'll get
"This loop invariant may not be maintained," because `0 <= i <= n` alone says nothing about what
`r` actually is.

## 5. A more interesting termination measure

`decreases n`, above, is a single `Int` counting down to 0 — the common case, but not the only
shape a termination argument takes. [`termination.rav`](./termination.rav) has Ackermann's
function, the textbook example for why:

```raven
func ackermann(m: Int, n: Int) returns (r: Int)
  decreases m, n
{
  m <= 0 ?
    n + 1 :
    (n <= 0 ? ackermann(m - 1, 1) : ackermann(m - 1, ackermann(m, n - 1)))
}
```

`decreases m, n` is a **lexicographic** measure — Raven treats the pair the way a dictionary
orders words: a recursive call is fine if `m` strictly decreases (whatever happens to `n`), or
if `m` stays exactly the same and `n` strictly decreases. No *single* `Int` can play this role
here: the innermost call, `ackermann(m, n - 1)`, leaves `m` completely untouched — only `n` goes
down. It's the call *around* it, `ackermann(m - 1, ...)`, that has to be trusted to bring `m`
down, regardless of whatever `ackermann(m, n - 1)` happens to return. Try
[`broken/ackermann_single_measure.rav`](./broken/ackermann_single_measure.rav) — the same
function with just `decreases m` — and watch it fail exactly on that inner call, with `This
decreases clause's termination measure may not decrease on this recursive call`: `m` really
doesn't decrease there, only `n` does, and a single-`Int` measure has no way to express "or the
other component decreased instead."

A comma-separated `decreases` clause works for any number of components, compared
lexicographically left to right, and each component's own type just needs *some* well-founded
order Raven already knows about — `Int` (bounded below by 0, exactly as `decreases n` already
relies on), or one you define yourself. Part 3 comes back to that second option, once the module
system needed to express it is in view.

## 6. Algebraic data types

```raven
type Outcome = data {
  case ok(value: Int);
  case capped
}

func boundedNext(c: Int, cap: Int) returns (r: Outcome)
  ensures c >= cap ==> r == capped
  ensures c < cap ==> r == ok(c + 1)
{
  c >= cap ? capped : ok(c + 1)
}
```

`data` declares a sum type: `Outcome` is either `ok(value)` or `capped`. A nullary case like
`capped` can optionally take a trailing `()` at construction sites (`capped()`) — this tutorial
just omits it, since it's not doing anything a unary case's real argument does. This isn't an
idle example: it's the "saturating implementation" from this part's opening roadmap, a little
ahead of schedule. Part 3 gives `Counter` a second implementation, built around exactly this
idea, that stops counting at a cap instead of overflowing — `Outcome` (or a type just like it) is
what its `create`/`increment` operations will return there.

So far `Outcome` values only ever get *built*. Two constructs take one apart again.

The smaller one is `is`: `r is ok` is a `Bool` saying which case `r` was built with. It pairs
with plain field access — `r.value` reads the argument of an `ok`, which is only meaningful when
`r` really *is* an `ok`, so the two usually travel together:

```raven
ensures r is ok ==> v == r.value
```

`is` binds exactly like `==`, so it sits inside a larger formula without needing parentheses:
`r is ok && v > 0` and `r is ok ==> ...` both group the way you'd expect.

For a case with no arguments the two are interchangeable — `r is capped` and the `r == capped`
that `boundedNext` above already used say exactly the same thing. `is` earns its keep on cases
that *do* carry arguments, where the equality you'd otherwise write has to reconstruct the value
field by field: `r == ok(r.value)`.

Writing a whole case analysis that way gets tedious, though, and inside a function body you'd
reach for `match` instead — it picks the case *and* names its arguments in one step:

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

Each arm names a case and binds one variable per argument — `n` above is the `Int` inside an
`ok`, in scope only for that arm's body. A nullary case binds nothing and takes no parentheses,
hence the bare `case capped =>`. A `match` is an ordinary expression, so every arm has to produce
the same type, here the `Int` this `func` returns.

Raven checks that the arms are **exhaustive**: name every case exactly once, or end with a
catch-all `case _ =>` arm covering whatever's left. Forgetting one is a type error rather than a
silent gap that only shows up later as a failed proof. You can also write `_` in place of an
argument name when you don't need it (`case ok(_) => 0`).

That leaves `is` for the places a `match` arm can't reach — a contract, as above, or one branch
of a larger condition.

Naming an arm's pattern variable after the field it binds is fine, and often clearest —
`case ok(value) => ...` does not stop a later `r.value` from resolving. The `f` in `r.f` is a
field name looked up in `r`'s own type, not a reference to whatever `f` happens to mean nearby,
so it never collides with a variable of the same name.

## 7. Quantifiers, briefly

`recordVisitor` above already used a `forall`. Two things worth knowing now, in more depth once
Part 5 revisits quantifiers in the resource-owning setting:

- **The direction you're using a quantifier in matters more than which one you picked.**
  *Proving* a `forall` (e.g. in an `ensures` clause) is generally robust; *assuming* one (e.g. in
  a `requires` clause, or a loop invariant you're relying on rather than establishing) is
  generally not, especially carried across many loop iterations. For `exists` it's the mirror
  image: *assuming* one is robust, *proving* one can be finicky. So if you're stating "some
  property holds of at least one element" as something you need to *prove*, see if it can
  instead be phrased as an upper/lower bound (a `forall`) — [Exercise 3](#exercises) below is
  built around exactly this choice. None of this is a hard rule, just a strong enough default to
  reach for first; used without any thought, quantifiers of either shape can degrade solver
  performance or cause outright timeouts, a topic Part 5 comes back to.
- **Triggers.** The curly braces in a quantifier, right after the bound variables, are a hint
  telling Z3 *which* terms should cause it to re-instantiate the quantifier (a technique called
  E-matching) — full syntax, from [Exercise 3](#exercises)'s solution:

  ```raven
  ensures forall j: Int :: {counts[j]} 0 <= j && j < len ==> counts[j] <= r
  ```

  `j` is the bound variable, `{counts[j]}` is the trigger, and `0 <= j && j < len ==> counts[j]
  <= r` is the body — Z3 will consider instantiating this `forall` at a specific value of `j`
  whenever the term `counts[j]` (for that same value) shows up elsewhere in the proof. You'll see
  this show up wherever a `forall` ranges over something indexed, like a `Map`. You don't need to
  fully understand triggers yet — just recognize the curly-brace syntax and know it's there to
  help the solver, not to change what the formula means.

## Why this matters for concurrency

None of this chapter is concurrency-specific — that's the point. Everything here is standard
Hoare logic over plain values, and if you've used an auto-active verification tool before,
nothing here should have surprised you. Part 2 is where Raven's reasoning starts to diverge from
that familiar ground, and that divergence — ownership, fractional permissions, the separating
conjunction — is exactly the machinery that makes concurrent reasoning possible later. Nothing
is wasted, but nothing distinctive has happened yet either.

## Debugging Corner

Raven distinguishes, via the diagnostic's bracketed kind prefix, "doesn't type-check" from
"doesn't verify" — worth deliberately triggering both once if you haven't already (Part 0
showed one of each). For a loop invariant specifically, Raven also distinguishes *which* half
failed:

- **"This loop invariant may not hold upon loop entry"** — your invariant is wrong even before
  the loop starts running (often: you forgot to account for the loop's initialization code).
- **"This loop invariant may not be maintained"** — it holds going in, but running the loop body
  once breaks it (often: the invariant is too weak to survive a single iteration).

These are two different bugs with two different fixes, and the message tells you which one
you're looking at — no need to guess.

## Exercises

Each exercise lives in `exercises/` as a stub with a deliberately incomplete
loop invariant (`invariant true // TODO`); fill it in until "Raven: Verify File" turns green.
Checked solutions are in `solutions/` if you get stuck or want to check your
answer — no shame in looking, this isn't a test.

1. **[`sum_range.rav`](./exercises/sum_range.rav)** — sum of `1 + 2 + ... + n`.
2. **[`gcd.rav`](./exercises/gcd.rav)** — gcd via repeated subtraction.
3. **[`hot_day.rav`](./exercises/hot_day.rav)** — the busiest day in a per-day hit log,
   deliberately designed to reward the `forall`-over-`exists` preference from §7 above.

## What's next

[Part 2](../02-ownership/) puts this same counter on the heap — one `field`, one `Ref` — and
asks what it even *means* to own a piece of mutable state.
