# Appendix B: Coming From Viper, Dafny, or Iris

A quick dictionary, not a full comparison — if you already know one of these tools, this is
meant to shortcut your intuition to the nearest Raven concept.

## From Viper {#sec:from-viper}

Viper's own field/heap model is exactly the same as Raven's — a field access is a permission
plus a value, and fractional permissions work identically in both. What Raven adds on top is
*ghost fields*: fields whose values come from a user-definable resource algebra rather than a
plain type, which is what everything from Part 4 onward is built on.

| Viper | Raven | Note |
|---|---|---|
| `acc(x.f)` | `own(x.f, v)` | Raven's `own` names the value too, not just the permission. |
| `acc(x.f, perc)` | `own(x.f, v, q)` | Same fractional-permission model. |
| (no direct equivalent) | `own(x.g, a)`, `g` a ghost field | `a` here is an element of whatever user-definable resource algebra `g`'s declared type names (Part 4) — a fact about proof-only state with its own composition rule, not just a permission on an ordinary value. Viper has no ghost fields and no notion of a resource algebra at all; this is the other half of what Raven adds on top of Viper's own field/heap model. |
| `predicate`, `fold`/`unfold` | `pred`, `fold`/`unfold` | Directly analogous. |
| (no direct equivalent) | `inv` | Viper has no built-in shared-invariant concept — front-ends targeting Viper that need concurrency encode it themselves on top. This is one of Raven's central additions. |
| macros | `auto pred` | Automatically inlined, no fold/unfold. |
| `inhale`/`exhale` | `inhale`/`exhale` | Same ghost statements, same role — Raven's own compilation pipeline reduces everything else down to exactly these two, the same way Viper's does. |
| `domain` | ADTs (`data`), or the module system | A Viper `domain` is closest to a restricted `interface`: a rep type plus axioms characterizing it, but no functors, no implementations, no functor composition. For a simple algebraic sum type, Raven's `data` is the direct match; for anything with more structure (a domain used to axiomatize a whole data structure), Raven's module system is the more general — and more capable — analogue. |
| quantified permissions | iterated separating conjunctions (Part 5c) | Raven's ISC design is explicitly built on Viper's, generalized to arbitrary resource algebras rather than just permissions. |
| magic wand (`A --* B`) | *(not currently supported)* | A magic wand asserts "give up `A` and you get `B` back" — handy for partially unfolding a recursive predicate (walk partway into a linked list, leave a wand behind that remembers how to fold it back up once you're done with the part you unfolded) without committing to the whole structure at once. Raven has no equivalent construct yet; the same traversals are instead written by carrying the "rest of the structure" explicitly as a separate resource, which is more verbose but doesn't need anything new. |
| `decreases e1, ..., en` | `decreases e1, ..., en` | Same contract syntax, same lexicographic-tuple concept — but Viper has no equivalent of Raven's user-definable `WellFoundedOrder` instances (Part 3). |
| no built-in concurrency | invariants, ghost fields/RAs, atomic contracts, prophecy variables | The actual gap Raven is designed to fill; see the Part 4/5 story in this tutorial, and Appendix D for prophecies specifically. |

There is one other deeper design difference worth knowing about:
Viper is built on *implicit dynamic frames*, a close cousin of separation logic where
expressions — in both programs and specifications — can be heap-dependent. Raven instead keeps
expressions pure everywhere; a heap read is always a statement (`val x := e.f;`), never buried
inside a larger expression. That restriction is what lets Raven treat evaluating an expression as
happening in one atomic step, no matter how many sub-terms it has — no other thread can observe
or interfere with it partway through, by a Lipton-style reduction argument — and Raven gets that
reasoning for free, rather than as something a concurrency proof has to establish itself. It's a
real part of why Raven's pure-expression design is a better fit for concurrency than Viper's.

## From Dafny {#sec:from-dafny}

| Dafny | Raven | Note |
|---|---|---|
| `method`/`function` | `proc`/`func` | Same split: side-effecting vs. pure-and-spec-usable. |
| `requires`/`ensures` | `requires`/`ensures` | Same. |
| loop `invariant` | loop `invariant` | Same concept — but Raven also has a *completely different*, unrelated use of the word `invariant` for shared concurrent state (`inv`); don't conflate the two just because Dafny only needs the first. |
| `decreases` | `decreases` | Same role, for recursive `func`/`lemma` termination — see {{ref sec:control-flow}}. |
| classes, `this` | heap-allocated objects via `field`/`Ref`, no implicit `this` | Dafny's memory model already assumes ownership tracking under the hood; Raven makes ownership the explicit thing you reason about, which is the entire subject of Part 2. |
| `datatype` | `data` | Same idea, algebraic sum types. |
| `modifies` | (implicit, via `own`) | The deeper difference, not just a syntax swap: Dafny is classical Hoare logic — there's no notion of a "heap resource," or any resource at all. Frame conditions have to be stated explicitly, by hand, via `modifies`; Raven's ownership model (Part 2) makes framing a *consequence* of what you own, rather than something you separately declare. |
| no built-in concurrency | invariants, ghost fields/RAs, atomic contracts | Dafny is sequential-only; this is the single biggest thing to unlearn coming from it — see Part 4's "why this matters for concurrency" callouts throughout Parts 1–3. |
| compiles to executable code | *(no compilation backend)* | Dafny compiles verified programs to real executables (C#, Java, Go, Python, JS, take your pick). Raven, as of this writing, is purely a verification language — there's no backend that turns a verified `.rav` file into something you run; the point is checking a design or an algorithm's correctness, not producing a deployable artifact from it. |

## From Iris {#sec:from-iris}

If you know Iris, you already know the *ideas* behind Parts 2–5 — ownership, shared invariants,
resource algebras (Iris's *cameras*, restricted here to Iris's simpler, non-step-indexed
unital-RA fragment), atomic triples. What Raven adds is automation: everything you'd build by
hand in the Iris Proof Mode inside Rocq is instead compiled down to a first-order SMT query and
discharged by Z3. Concretely:

| Iris | Raven |
|---|---|
| Invariant `Inv N P` | `inv` |
| A camera | A resource algebra implementing `Library.ResourceAlgebra` (Appendix A) — deliberately the *non*-step-indexed, non-higher-order fragment of Iris's cameras, since that's what stays SMT-automatable. |
| Atomic triple `<< P >> e << v, Q >>` | `atomic requires`/`atomic ensures` (Part 5b) |
| Ghost state ownership `own γ a` | `ghost field`, `own(e.g, v)` |
| Frame-preserving update | `fpu` |
| View shift / mask-aware invariant opening | Raven's atomicity analysis, checked automatically rather than proved by hand each time |

The trade-off, honestly: Raven's fragment is deliberately *less* expressive than full Iris —
no impredicative invariants, no step-indexing, no higher-order ghost state. That's what makes it
automatable; landmark, foundational proofs like RustBelt still need full Iris in Rocq. Raven is
aimed at the more common case of everyday concurrent data structure proofs that don't.
