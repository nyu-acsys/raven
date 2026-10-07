# Coming From Viper, Dafny, or Iris

This is a quick dictionary, not a full comparison. If you already know one of these tools, it
should help you quickly find the nearest Raven concept.

## From Viper {#sec:from-viper}

Viper's field/heap model is exactly the same as Raven's. A field access is a permission plus a
value, and fractional permissions work identically in both. What Raven adds on top is *ghost
fields*, i.e., fields whose values come from a user-definable resource algebra rather than a
plain type, which is what everything from Part 4 onward is built on.

| Viper | Raven | Note |
|---|---|---|
| `acc(x.f)` | `own(x.f, v)` | Raven's `own` names the value too, not just the permission. |
| `acc(x.f, perc)` | `own(x.f, v, q)` | Same fractional-permission model. |
| (no direct equivalent) | `own(x.g, a)`, `g` a ghost field | `a` here is an element of whatever user-definable resource algebra `g`'s declared type names (Part 4). It is a fact about proof-only state with its own composition rule, not just a permission on an ordinary value. Viper has no ghost fields and no notion of a resource algebra at all. This is the other half of what Raven adds on top of Viper's own field/heap model. |
| `predicate`, `fold`/`unfold` | `pred`, `fold`/`unfold` | Directly analogous. |
| (no direct equivalent) | `inv` | Viper has no built-in shared-invariant concept. Front-ends targeting Viper that need concurrency encode it themselves. This is one of Raven's central additions. |
| macros | `inline pred` | Automatically inlined, no fold/unfold. |
| `inhale`/`exhale` | `inhale`/`exhale` | Same ghost statements, same role. Raven's compilation pipeline reduces everything else to exactly these two, just like Viper's does. |
| `domain` | ADTs (`data`), or the module system | A Viper `domain` is closest to a restricted `interface`: a rep type plus axioms characterizing it, but no functors, no implementations, and no functor composition. For a simple algebraic sum type, Raven's `data` is the direct match. For anything with more structure (a domain used to axiomatize a whole data structure), Raven's module system is the more general and more capable analogue. |
| `Seq[T]` | `Library.Seq[E]` ({{ref app:stdlib-types}}) | The same operations and axioms, written as functions: `append(s, t)` for `s ++ t`, `length(s)` for `\|s\|`, `index(s, i)` for `s[i]`, and so on. Unlike in Viper, `==` on sequences isn't extensional by itself; assert `equal(s, t)` first. |
| quantified permissions | iterated separating conjunctions (Part 5.3) | Raven's ISC design is explicitly built on Viper's, generalized to arbitrary resource algebras rather than just permissions. |
| magic wand (`A --* B`) | *(not currently supported)* | A magic wand asserts "give up `A` and you get `B` back." This is handy for partially unfolding a recursive predicate (walk partway into a linked list, and leave a wand behind that remembers how to fold it back up once you're done with the part you unfolded) without committing to the whole structure at once. Raven has no equivalent construct yet. The same traversals are instead written by carrying the "rest of the structure" explicitly as a separate resource, which is more verbose but doesn't need anything new. |
| `decreases e1, ..., en` | `decreases e1, ..., en` | Same contract syntax, same lexicographic-tuple concept. However, Viper has no equivalent of Raven's user-definable `WellFoundedOrder` instances (Part 3). |
| no built-in concurrency | invariants, ghost fields/RAs, atomic contracts, prophecy variables | The gap Raven is designed to fill. See Parts 4 and 5 in this tutorial, and {{ref app:where-next}} for prophecies specifically. |

There is one other, deeper design difference worth knowing about. Viper is built on *implicit
dynamic frames*, a close relative of separation logic in which expressions (in both programs and
specifications) can be heap-dependent. Raven instead keeps expressions pure everywhere. A heap
read is always a statement (`val x := e.f;`), never part of a larger expression. This restriction
is what lets Raven treat the evaluation of an expression as happening in one atomic step, no
matter how many sub-terms it has. By a Lipton-style reduction argument, no other thread can
observe or interfere with it partway through. Raven gets that reasoning for free, rather than as
something a concurrency proof has to establish itself. This is an important part of why Raven's
pure-expression design is a better fit for concurrency than Viper's.

## From Dafny {#sec:from-dafny}

| Dafny | Raven | Note |
|---|---|---|
| `method`/`function` | `proc`/`func` | Same split: side-effecting vs. pure-and-spec-usable. |
| `requires`/`ensures` | `requires`/`ensures` | Same. |
| loop `invariant` | loop `invariant` | Same concept. However, Raven also uses the word "invariant" in a *completely different*, unrelated sense for shared concurrent state (`inv`). Don't conflate the two just because Dafny only needs the first. |
| `decreases` | `decreases` | Same role, for recursive `func`/`lemma` termination. See {{ref sec:control-flow}}. |
| classes, `this` | heap-allocated objects via `field`/`Ref`, no implicit `this` | Dafny's memory model already assumes ownership tracking under the hood. Raven makes ownership the explicit thing you reason about, which is the subject of Part 2. |
| `datatype` | `data` | Same idea, algebraic sum types. |
| `modifies` | (implicit, via `own`) | This is a deeper difference, not just a change in syntax. Dafny is based on classical Hoare logic, with no notion of a "heap resource," or any resource at all. Frame conditions have to be stated explicitly, by hand, via `modifies`. Raven's ownership model (Part 2) makes framing a *consequence* of what you own, rather than something you separately declare. |
| no built-in concurrency | invariants, ghost fields/RAs, atomic contracts | Dafny is sequential-only. This is the biggest thing to unlearn when coming from Dafny. See the "Why this matters for concurrency" sections throughout Parts 1–3. |
| compiles to executable code | *(no compilation backend)* | Dafny compiles verified programs to real executables (C#, Java, Go, Python, JS). Raven, as of this writing, is purely a verification language. There's no backend that turns a verified `.rav` file into something you can run. The goal is to check a design or an algorithm's correctness, not producing a deployable artifact from it. |

## From Iris {#sec:from-iris}

If you know Iris, you already know the *ideas* behind Parts 2–5: ownership, shared invariants,
resource algebras (Iris's *cameras*, restricted here to Iris's simpler, non-step-indexed
unital-RA fragment), and atomic triples. What Raven adds is automation. Everything you'd build by
hand in the Iris Proof Mode inside Rocq is instead compiled down to a first-order SMT query and
discharged by Z3. Concretely:

| Iris | Raven |
|---|---|
| Invariant `Inv N P` | `inv` |
| A camera | A resource algebra implementing `Library.ResourceAlgebra` ({{ref app:resource-algebras}}). This is deliberately the *non*-step-indexed, non-higher-order fragment of Iris's cameras, since that's what stays SMT-automatable. |
| Atomic triple `<< P >> e << v, Q >>` | `atomic requires`/`atomic ensures` (Part 5.2) |
| Ghost state ownership `own γ a` | `ghost field`, `own(e.g, v)` |
| Frame-preserving update | `fpu` |
| View shift / mask-aware invariant opening | Raven's atomicity analysis, checked automatically rather than proved by hand each time |

There is a trade-off. Raven's fragment is deliberately *less* expressive than full Iris. It has
no impredicative invariants, no step-indexing, and no higher-order ghost state. That's what makes
it automatable. Landmark, foundational proofs like RustBelt still need full Iris in Rocq. Raven
is aimed at the more common case of everyday concurrent data structure proofs that don't.
