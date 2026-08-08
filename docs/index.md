---
layout: home

hero:
  name: Raven
  text: Concurrency reasoning, built in
  tagline: An intermediate verification language and SMT-based deductive verifier for fine-grained concurrent programs, founded on concurrent separation logic.
  image:
    src: /logo.png
    alt: Raven
  actions:
    - theme: brand
      text: Start the tutorial
      link: /tutorial/
    - theme: alt
      text: Install
      link: /tutorial/getting-started/#install
    - theme: alt
      text: GitHub
      link: https://github.com/nyu-acsys/raven

features:
  - title: Concurrency as a first-class citizen
    details: Shareable invariants, atomic specifications, and user-definable resource algebras — the reasoning principles of modern concurrent separation logic, available directly in the language rather than encoded into it.
  - title: Automated, but predictable
    details: Verification conditions are discharged by Z3. The logic is deliberately restricted — no higher-order quantification, impredicativity, or step-indexing — so that automation stays robust and failures stay diagnosable.
  - title: Proofs alongside code
    details: Ghost code, invariants, and proof steps are interleaved with the program they describe, so a program and its correctness argument are developed together rather than after the fact.
  - title: Built to be extended
    details: A documented extension API lets you add your own types, expressions, statements, and contract clauses — turning Raven into an IVL targeted at your own source language or domain.
---

## What Raven is

Raven is an **intermediate verification language** (IVL) and an SMT-based deductive verifier
for it. It occupies the same layer as [Boogie](https://www.microsoft.com/en-us/research/project/boogie-an-intermediate-verification-language/),
[Why3](https://www.why3.org/), and [Viper](https://www.pm.inf.ethz.ch/research/viper.html) — a
target that front-end tools compile *to*, rather than a language you ship production code in —
but it treats concurrency as a first-class concern rather than something layered on afterwards.

It is also usable directly, and is designed to be teachable: the [tutorial](/tutorial/) takes a
single running example from a plain integer to a lock-protected object shared across threads.

Raven's metatheory is based on the [Iris](https://iris-project.org/) separation logic framework.
Iris' more expressive features — higher-order quantification, impredicativity, step-indexing —
are deliberately left out, and complementary features such as a higher-order module system are
added to recover expressivity. The result is a logic strong enough for realistic concurrent
algorithms while remaining amenable to SMT automation.

## A first look

Two threads increment a shared counter, in an interleaving neither of them controls. A *shared
invariant* is what makes that tractable: a fact about the counter that every thread agrees to
restore after each atomic step, and that any of them may rely on:

```raven
field count: Int

// A shared invariant: a fact about `c.count` that has to hold after every
// atomic step, whichever thread just took it. Any thread that knows about `c`
// may open it, for exactly one atomic step at a time.
inv evenCount(c: Ref) {
  exists v: Int :: own(c.count, v) && v % 2 == 0
}

// `faa` (fetch-and-add) is a single indivisible step, which is what makes it
// legal to perform while the invariant is open.
proc bumpTwice(c: Ref)
  requires evenCount(c)
{
  unfold evenCount(c);
  val _ := faa(c.count, 2);
  fold evenCount(c);
}

proc client(c: Ref)
  requires evenCount(c)
{
  spawn bumpTwice(c);
  spawn bumpTwice(c);

  unfold evenCount(c);
  val x := c.count;
  assert x % 2 == 0;
  fold evenCount(c);
}
```

The final `assert` holds under *every* interleaving of the two spawned threads with this one, and
nothing in the proof mentions interleavings at all. Note also what the invariant is not: unlike a
predicate, it is ambient and freely duplicable — both threads and the client hold it at once —
and it may be opened for exactly one atomic step, which is why `faa` is allowed inside and an
ordinary read would not be.

Underneath this sits ownership: `own(c.count, v)` is a resource, not a fact, and the separating
conjunction between two such assertions means *disjoint* ownership, ruling out aliasing by
construction. The [tutorial](/tutorial/) builds all of it up from a single-threaded counter.

## For researchers

Raven's design, metatheory, and empirical evaluation are described in:

> **Raven: An SMT-Based Concurrency Verifier**
> Ekanshdeep Gupta, Nisarg Patel, and Thomas Wies.
> *Computer Aided Verification (CAV), 2025.*
> [10.1007/978-3-031-98668-0_4](https://doi.org/10.1007/978-3-031-98668-0_4)

The repository carries a growing
[collection of verified concurrent data structures](https://github.com/nyu-acsys/raven/tree/main/test/concurrent) —
spin and ticket locks, a Treiber stack, atomic counters, and B+-tree templates among them — most
drawn from the literature or from real systems. These double as a regression suite and as worked
examples of the proof patterns Raven is meant to support.

If you are building a verification tool of your own, the
[extension API](https://github.com/nyu-acsys/raven/blob/main/docs/ext/README.md) is the intended
entry point: it lets you add syntax and proof constructs without forking the pipeline, and ships
with several extensions — termination checking via `decreases`, Iris-style prophecy variables,
and Eris-style error credits for probabilistic reasoning — as worked references.

## Getting started

The quickest route is the **Raven Verifier** extension for VS Code, which bundles the verifier
and Z3; [Part 0 of the tutorial](/tutorial/getting-started/) walks through installing it and
verifying a first file. To build from source instead:

```bash
$ git clone https://github.com/nyu-acsys/raven.git
$ cd raven
$ opam switch create raven 5.2.0
$ eval $(opam env)
$ opam install . --deps-only --with-test
$ dune build && dune runtest
```

Raven requires [opam](https://opam.ocaml.org/) (>= 2.1.0), OCaml 5.x, and
[Z3](https://github.com/Z3Prover/z3) (>= 4.13.0).

## Team

Raven is developed at the [ACSys](https://github.com/nyu-acsys) group at New York University by

- **Ekanshdeep Gupta**
- **Nisarg Patel**
- **Thomas Wies**

with further contributions from
[everyone who has worked on the repository](https://github.com/nyu-acsys/raven/graphs/contributors).

<div style="margin-top: 3rem; text-align: center; opacity: 0.7; font-size: 0.9em;">

Raven is MIT-licensed and developed in the open at
[github.com/nyu-acsys/raven](https://github.com/nyu-acsys/raven).

</div>
