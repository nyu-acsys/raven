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

> This tutorial has been created with the help of generative AI. The materials have been
> carefully reviewed by the tool authors for accuracy and correctness.

This tutorial teaches Raven — an intermediate verification language (IVL) and SMT-based
deductive verifier for concurrent separation logic — through the VS Code extension ("Raven
Verifier", searchable from within VS Code's Extensions panel;
see [Part 0](./00-getting-started/) for install steps), the way most people actually use the
tool. One example, a hit counter, grows across Parts 1 through 4: a plain value, then a
heap-allocated object, then an interface with more than one implementation, then a concurrent
data structure whose proof requires ghost-state reasoning. Part 5 then closes the tutorial with
three full case studies — fork/join, a ticket lock, and an array of independently-lockable
counters — that put everything from Parts 1–4 to work at once.

Every code listing in this tutorial is a real `.rav` file, checked against the actual `raven`
binary — open any of them yourself and run it. `broken/` subdirectories contain examples that are
*supposed* to fail — read their comments before running them. `exercises/` subdirectories contain
stubs with a deliberate gap for you to fill in; `solutions/` has checked answers.

## Contents

- **[0. Getting Started](./00-getting-started/)** — installing the VS Code extension, reading
  your first diagnostic, the one habit (reading related-location information, not just the
  first line of a failure) every later part leans on.
- **[1. Sequential Raven](./01-sequential/)** — values, `func` vs. `proc`, control flow,
  recursion, algebraic data types, a first taste of quantifiers. No heap yet.
- **[2. Ownership and Resources](./02-ownership/)** — fields, `own`, separating conjunction,
  fractional permissions, the frame rule, anti-aliasing. Still single-threaded.
- **[3. The Module System](./03-modules/)** — interfaces, abstract predicates as a
  specification boundary, axioms, functors. Reorganizing what Parts 1–2 already taught, not new
  reasoning.
- **[4. Ghost Code and Basic Concurrency](./04-ghost-and-concurrency/)** — threads, atomic
  primitives, shared invariants, ghost fields, resource algebras, frame-preserving updates. This
  is where Raven stops resembling a purely sequential program verifier.
- **[5. Scaling Up](./05-advanced/)** — three capstones and a reference chapter:
  - **[5a. Capstone: Fork/Join](./05-advanced/fork-join/)** — a hand-rolled resource algebra and
    the module system from Part 3, put to work on a one-shot ownership handoff between two
    threads, built up from a first attempt that doesn't work.
  - **[5b. Atomic Contracts](./05-advanced/atomic-contracts/)** — a ticket lock, proved twice:
    once with a plain invariant, once with an atomic contract.
  - **[5c. Iterated Separating Conjunctions](./05-advanced/iterated-star/)** — a shelf of
    independently-lockable counters, owned via one invariant regardless of the shelf's size.
  - **[5d. Automation Features](./05-advanced/automation/)** — implicit parameters, witness
    computation, `auto` lemmas/predicates, triggers, `assert ... with`, and a checklist for
    "my proof just hangs."

## Appendices

- **[A. Resource Algebras, Formally](./appendix/resource-algebras.md)**
- **[B. Coming From Viper, Dafny, or Iris](./appendix/from-other-tools.md)**
- **[C. Beyond This Tutorial: the Extension API](./appendix/extension-api.md)**
- **[D. Where to Go Next](./appendix/where-next.md)**

## Prerequisites

Working knowledge of an imperative language, and some prior exposure to Hoare-style
pre/postconditions (a semester of formal methods, or having skimmed a [Dafny](https://dafny.org/)
or [Viper](https://viper.ethz.ch/) tutorial, is enough). No separation logic, Iris, or
concurrency background assumed — Part 2 builds ownership reasoning from scratch, Part 4 builds
shared-invariant reasoning from scratch.

If you already have that background and want to skip straight to Part 5's capstones, each opens
with a one-line "Assumes" pointer to the specific earlier sections it relies on, rather than
re-teaching them.
