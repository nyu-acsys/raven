# Appendix B: Adding a Hardware Primitive

*Assumes: {{ref sec:threads-and-atomics}} (atomic heap operations), Part 3 (interfaces and
functors), and {{ref sec:au-mechanics}} (atomic contracts and `bindAU`/`openAU`/
`commitAU`).*

Part 4 introduced `faa` as one of "the atomic heap operations the standard library provides",
and said in passing that nothing about them is built into the language. This appendix makes
good on that: it shows what a new one costs to add, which is a functor and about fifteen lines
of ordinary Raven.

That matters beyond the convenience. A verifier whose atomic operations are fixed by its
implementation can only reason about the hardware its authors anticipated. If you are modelling
a machine with a primitive Raven has never heard of — or a *restricted* version of a familiar
one, or an operation that is atomic only on your target — you write it, in the language, and it
is as much a first-class citizen as `cas`.

The construct that makes this possible, `atomic { ... }`, is more general than the recipe it is
introduced by: it declares that any multi-step computation counts as one physical step, anywhere
in a program, and needs no primitive or functor around it.
{{ref sec:atomic-block-standalone}} covers that use on its own, and
{{ref sec:trust-boundary}} covers what you are taking on by writing it.

## What the library gives you, and what it doesn't {#sec:what-the-library-gives}

`Library.Atomics` provides `cas`, `cmpxchg` and `xchg` over any word-sized field;
`Library.IntAtomics` adds `faa` and inherits the other three at `Int` fields. Neither is
privileged. You can read the whole thing — it is about a hundred and thirty lines — with

```
raven --print-library-source lib/library/atomics.rav
```

It is worth reading before writing your own, because everything below is that file's shape
applied to a new operation.

Three interfaces set up the vocabulary. `Library.WordSized` marks a type with a machine-word
representation. It declares nothing but a representation type, because there is nothing it
*could* declare that would say "this fits in one word" — instead the front end checks the type
structurally at each use: `Int`, `Bool`, `Ref`, or a data type with at most four constructors
each carrying at most one of those. Try to use an atomic primitive on a `Map[Int, Int]` field
and you are told so, at the call site.

`Library.AtomicField` then bundles a field with its word-sized value type:

```raven
interface AtomicField {
  module E : WordSized
  field f : E
}
```

and `Library.IntField` refines `E` to `Int`, for primitives that need arithmetic or ordering.
A field parameter is what lets a primitive be verified *once*, against an abstract field,
rather than once per field it is ever used on.

## Anatomy of a primitive {#sec:anatomy}

`xchg` is the smallest complete example — an unconditional swap — so it shows the shape with
nothing else in the way. This is the library's own definition, verbatim:

```raven
proc xchg(x.A.f, new_val: A.E, implicit ghost v: A.E)
  returns (old_val: A.E)
  atomic requires own(x.A.f, v, 1.0)
  atomic ensures  own(x.A.f, new_val, 1.0) && old_val == v
{
  atomic {
    ghost val phi := bindAU();
    v := openAU(phi);

    old_val := x.A.f;
    x.A.f := new_val;

    commitAU(phi, old_val);
  }
}
```

Four things are doing work here, and they are worth separating because each is independently
useful:

**The location parameter, `x.A.f`.** It binds `x` as the `Ref` and names the field this
operates on. It is a destructuring binder, not a new kind of value — the field still comes from
the module parameter `A` — but it makes the declaration read the way the call site does.
Callers may pass either `xchg(c.count, 1)` or a bare `Ref`.

**The logically atomic contract.** `atomic requires` / `atomic ensures`, rather than plain
`requires` / `ensures`, is what lets a caller hold an invariant open across the call and commit
at the linearization point — {{ref sec:au-mechanics}} covers what that means and why
the ordinary kind is not enough.

**The physically atomic body, `atomic { ... }`.** The body reads the field and then writes it:
two steps. The contract promises one. The block is what reconciles them, declaring that the
whole body is a single machine step. It is not part of the primitive-writing recipe as such —
it is a general construct for asserting that a multi-step computation is one physical step, and
{{ref sec:atomic-block-standalone}} uses it with no primitive in sight.

**The implicit ghost `v`.** The caller never passes it. It stands for the value in the field at
the linearization point, and is solved for at each call site.

## Worked example: fetch-and-max {#sec:fetch-and-max}

Real hardware has a fetch-and-max; Raven's library does not. Here is the whole thing
([`fetch_and_max.rav`](./fetch_and_max.rav)):

```raven
module MaxOps[A: Library.IntField] {
  proc fetch_and_max(x.A.f, n: Int, implicit ghost v: Int)
    returns (old_val: Int)
    atomic requires own(x.A.f, v, 1.0)
    atomic ensures  own(x.A.f, v > n ? v : n, 1.0) && old_val == v
  {
    atomic {
      ghost val phi := bindAU();
      v := openAU(phi);

      old_val := x.A.f;
      if (old_val < n) { x.A.f := n; }

      commitAU(phi, old_val);
    }
  }
}
```

The parameter is `Library.IntField`, not `Library.AtomicField`, because comparing two values
needs an ordering and the weaker interface does not provide one. That distinction is the same
one that makes the library split into `Atomics` and `IntAtomics` in the first place.

A client never names an instantiation:

```raven
module HighWater {
  import MaxOps._

  field high: Int

  inv water(c: Ref) { exists n: Int :: own(c.high, n, 1.0) && n >= 0 }

  proc offer(c: Ref, k: Int)
    requires water(c) && k >= 0
  {
    unfold water(c);
    val prev: Int := fetch_and_max(c.high, k);
    fold water(c);
  }
}
```

`import MaxOps._` brings the members into scope with the functor's parameter still unsolved,
and the call `fetch_and_max(c.high, k)` solves it from `high` — the field its location argument
names. There is no `module M = MaxOps[...]` anywhere, and there is no way to write one for a
field declared this way: the instance is synthesized per field and is deliberately not
nameable, exactly as the per-field machinery behind `own` already is.

Two things are worth noticing about that client, because both are automation your primitive
inherits without asking for it.

The call sits between `unfold` and `fold`, i.e. with the invariant open, and that is legal
precisely because it costs *one* atomic step. Add a second call in the same window and the
atomicity analysis rejects the procedure — the same rule that governs `faa` in Part 4.

And neither the `unfold` nor the `fold` supplies a witness for `n`. It would be easy to assume
a hand-written primitive needs help here, and to write `fold water(c)[ n := ... ]` out of
caution; it does not. The value to fold back is read off the heap by the witness computation
({{ref sec:witness-computation}}), from the `own` in your `atomic ensures`, exactly as it would
be for any other procedure.

## Worked example: two locations at once {#sec:dcas}

Everything so far could have been a built-in statement. This could not.

Double compare-and-swap compares and writes two *independent* locations in one step — Motorola
68k `CAS2`, z/Architecture `PLO`. A built-in operates on the one field baked into it; a
procedure takes as many location parameters as it needs. From [`dcas.rav`](./dcas.rav):

```raven
module DCas[A: Library.AtomicField, B: Library.AtomicField] {
  proc dcas(x.A.f, y.B.f, old_a: A.E, new_a: A.E, old_b: B.E, new_b: B.E,
            implicit ghost va: A.E, implicit ghost vb: B.E)
    returns (b: Bool)
    atomic requires own(x.A.f, va, 1.0) && own(y.B.f, vb, 1.0)
    atomic ensures  own(x.A.f, (va == old_a && vb == old_b) ? new_a : va, 1.0)
                 && own(y.B.f, (va == old_a && vb == old_b) ? new_b : vb, 1.0)
                 && b == (va == old_a && vb == old_b)
  {
    atomic {
      ghost val phi := bindAU();
      va, vb := openAU(phi);

      val cur_a: A.E := x.A.f;
      val cur_b: B.E := y.B.f;
      if (cur_a == old_a && cur_b == old_b) {
        x.A.f := new_a;
        y.B.f := new_b;
        b := true;
      } else {
        b := false;
      }

      commitAU(phi, b);
    }
  }
}
```

Two field parameters, two location parameters, two implicit ghosts — so `openAU` hands back a
tuple. The client is a pair of fields an invariant keeps in step:

```raven
inv agreed(c: Ref) {
  exists l: Int, r: Int :: own(c.left, l, 1.0) && own(c.right, r, 1.0) && l == r
}
```

Without a two-location primitive there is no way to move both without passing through a state
where they disagree — which is precisely what this invariant forbids, and precisely what the
proof would catch. With one, `ok := dcas(c.left, c.right, 0, 1, 0, 1)` solves `A` from `left`
and `B` from `right`, independently, and the whole thing is one step. As in the previous
example, the surrounding `unfold`/`fold` need no witnesses — including for the fact that the
two fields still agree, whichever way the compare went.

This is also where the "not unsound, just unusable" property of aliased instantiation shows up:
`DCas` may be instantiated with both parameters at the *same* field, and the generic body still
verifies. The clash surfaces at the client, as a precondition asking for 2.0 permission on one
field. A call like that cannot be made — which is the right answer, since no hardware
double-CAS operates on one location twice.

## `atomic { }` on its own {#sec:atomic-block-standalone}

Everything so far has used `atomic { ... }` inside a primitive's body, which is where it is
most obviously needed. But it is not tied to that, and it is worth saying plainly: **it is the
general way to declare that a multi-step computation is a single physical step, and it can be
written wherever a step is being counted** — that is, wherever an invariant is open or an atomic
update is in flight. No functor, no contract, no procedure of its own.

If a pair of fields has to move together and you only need it in one place, you do not need
`dcas` at all ([`atomic_block.rav`](./atomic_block.rav)):

```raven
inv agreed(c: Ref) {
  exists l: Int, r: Int :: own(c.left, l, 1.0) && own(c.right, r, 1.0) && l == r
}

proc advance(c: Ref)
  requires agreed(c)
{
  unfold agreed(c);

  atomic {
    c.left := 1;
    c.right := 1;
  }

  fold agreed(c);
}
```

The body need not be writes, and need not be short: `double_both` in the same file reads a
field, computes with it, and writes both — four statements, one step.

Remove the block and Raven objects, which is the whole point
([`broken/no_atomic_block.rav`](./broken/no_atomic_block.rav)):

```
Verification Error: Attempting to take more than one atomic step with an open
invariant or atomic update.
```

That error is not bureaucratic. Two writes are two steps, so between them there is a state
where `left` and `right` disagree, and another thread holding the same invariant could observe
it — which is exactly what `agreed` claims is impossible. What the block buys is not a proof
that the two writes are indivisible. It is permission to assume it.

This is what makes `atomic { }` a modelling tool rather than a library-authoring one. Use it to
stand in for anything your platform provides that Raven cannot see: a wide aligned store, an
interrupt-masked region on a single-core device, a transactional-memory block, a system call, a
lock-free routine from a library you are taking as given. Raven does not distinguish between
them, and cannot check any of them — which is the subject of the next section.

## Where the trust boundary is {#sec:trust-boundary}

`atomic { ... }` is not checked. It cannot be: Raven has no model of your target machine's
instruction set, and unlike a model checker it has no scheduler to enforce a claim about
interleaving. When you write it you are asserting that the enclosed code compiles to something
indivisible, and the verifier believes you.

That is a real obligation, and it is worth being precise about who carries it. Everything else
in a Raven proof is checked; this is the one place anyone — a primitive's author or an ordinary
procedure modelling a platform guarantee — adds an axiom about the world. The library's four
primitives make exactly the same assertion, and are not more trustworthy for being in the
library, only more reviewed. A block you write inline in a procedure body is not a lesser claim
than one inside a functor; it is the same claim, with less around it.

Two practical consequences. Keep the block as small as the operation genuinely is: every extra
statement inside is extra trust, and the block does not care whether the code inside is
plausibly one instruction. And be wary of loops or recursion inside one, where "a single machine
step" is least credible — Raven permits it without complaint.

Because these are assumptions rather than results, `--strict` reports them:

```
$ raven --strict my_program.rav
[Warning] File "my_program.rav", line 33, column 2 to line 36, column 3:
33 |   atomic {
       ^^^^^^^^
this `atomic` block's body is assumed to be a single machine step, not checked;
Raven has no model of the target machine to verify that against
```

That is the same flag that reports an explicit `free` and a missing `decreases`, and for the
same reason: it enumerates everything a proof rests on that the proof did not establish. One
warning per block, wherever it appears.

A program that merely calls `cas` is not warned about a block it did not write — but not
because of anything specific to `atomic { }`. The standard library is loaded once per run with
every concrete procedure's body stripped before type-checking even begins, since it is trusted
rather than reverified for each program; `cas`'s block is gone by the time this check runs, the
same as everything else in its body. Check `lib/library/atomics.rav` itself as an ordinary
program, rather than importing it, and its bodies are intact and its blocks are flagged like
anyone else's (`lib/library/library.t` in the repository pins exactly that).

## When you need the Extension API instead {#sec:when-extension-api}

Everything above is written *in* Raven. You need the
[Extension API](../extension-api.md) only when you want new **syntax** — a new form of type, expression,
statement, or contract clause that the parser does not have. A new *operation*, however exotic
its semantics, is a procedure.

The practical test: if you can express what your primitive does with a contract over `own`, and
the reader is willing to write `my_op(x.f, ...)` rather than a bespoke keyword, you do not need
the Extension API. If you need `my_op x.f <- e` to parse, you do.
