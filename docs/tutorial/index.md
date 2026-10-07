<script setup>
import { withBase } from 'vitepress'
</script>

<table>
<tr>
<td width="200"><img width="200" :src="withBase('/logo.png')" alt="Raven"/></td>
<td>

# The Raven Tutorial

*Concurrency reasoning, built in from lesson one.*

</td>
</tr>
</table>

> This tutorial has been created with the help of generative AI. It has been
> carefully reviewed by the tool authors for accuracy and correctness.

This tutorial teaches Raven, an intermediate verification language (IVL) and SMT-based
deductive verifier for concurrent separation logic. It works through the VS Code extension
("Raven Verifier", searchable from within VS Code's Extensions panel, see
[Part 0](./getting-started/) for install steps), which is how most people actually use the
tool. A single example, a hit counter, grows across Parts 1 through 4. It starts as a plain
value, becomes a heap-allocated object, then an interface with more than one implementation, and
finally a concurrent data structure whose proof requires ghost-state reasoning. Part 5 closes the
tutorial with four full case studies that put everything from Parts 1–4 to work at once:
fork/join, a ticket lock, an array of independently-lockable counters, and a distributed counter
proved with prophecy variables.

Every code listing in this tutorial is a real `.rav` file, checked against the actual `raven`
binary, so you can open any of them and run it yourself. The `broken/` subdirectories contain
examples that are *supposed* to fail. Read their comments before running them. The `exercises/`
subdirectories contain stubs with a deliberate gap for you to fill in, and `solutions/` has
checked answers.

## Contents

- **[0. Getting Started](./getting-started/)**: installing the VS Code extension, reading
  your first diagnostic, and the one habit every later part leans on (reading related-location
  information, not just the first line of a failure).
- **[1. Sequential Raven](./sequential/)**: values, `func` vs. `proc`, control flow,
  recursion, algebraic data types, a first taste of quantifiers. No heap yet.
- **[2. Ownership and Resources](./ownership/)**: fields, `own`, separating conjunction,
  fractional permissions, the frame rule, anti-aliasing. Still single-threaded.
- **[3. The Module System](./modules/)**: interfaces, abstract predicates as a
  specification boundary, axioms, functors. This part reorganizes what Parts 1–2 already taught
  rather than introducing new reasoning.
- **[4. Ghost Code and Basic Concurrency](./ghost-and-concurrency/)**: threads, atomic
  primitives, shared invariants, ghost fields, resource algebras, frame-preserving updates. This
  is where Raven stops resembling a purely sequential program verifier.
- **[5. Scaling Up](./advanced/)**: four capstones and a reference chapter.
  - **[5.1. Capstone: Fork/Join](./advanced/fork-join/)**: a hand-rolled resource algebra and
    the module system from Part 3, put to work on a one-shot ownership handoff between two
    threads. The proof is built up starting from a first attempt that doesn't work.
  - **[5.2. Atomic Contracts](./advanced/atomic-contracts/)**: a ticket lock, proved twice,
    once with a plain invariant and once with an atomic contract.
  - **[5.3. Iterated Separating Conjunctions](./advanced/iterated-star/)**: a shelf of
    independently-lockable counters, owned via one invariant regardless of the shelf's size.
  - **[5.4. Capstone: Prophecies](./advanced/prophecies/)**: a distributed counter whose `get`
    doesn't always know its own linearization point without help from a concurrent `incr`. The
    solution uses prophecy variables and a "helping protocol" that combines one-shot handoffs,
    atomic contracts, and an ISC over a set.
  - **[5.5. Automation Features](./advanced/automation/)**: implicit parameters, witness
    computation, `auto` lemmas, triggers, inline predicates and functions, `assert ... with`, and
    a checklist for "my proof just hangs."

## Appendices

- **{{ref app:resource-algebras}}: Resource Algebras, Formally**
- **{{ref app:hardware-primitives}}: Adding a Hardware Primitive**: writing an atomic
  operation the standard library doesn't provide, in ordinary Raven.
- **{{ref app:stdlib-types}}: Standard Library Data Types**: options, lists, sequences,
  and arrays.
- **{{ref app:from-other-tools}}: Coming From Viper, Dafny, or Iris**
- **{{ref app:extension-api}}: Beyond This Tutorial: the Extension API**
- **{{ref app:where-next}}: Where to Go Next**

## Prerequisites

You should have working knowledge of an imperative language and some prior exposure to
Hoare-style pre/postconditions (a semester of formal methods, or having skimmed a
[Dafny](https://dafny.org/) or [Viper](https://viper.ethz.ch/) tutorial, is enough). No
background in separation logic, Iris, or concurrency is assumed. Part 2 builds ownership
reasoning from scratch, and Part 4 does the same for shared-invariant reasoning.

If you already have that background and want to skip straight to Part 5's capstones, note that
each one opens with a one-line "Assumes" pointer to the specific earlier sections it relies on,
so you can look those up as needed.
