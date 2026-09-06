<p align="center">
  <img width="100%" src=".github/assets/banner.png" alt="Raven Verifier"/>
</p>

<p align="center">
  <img alt="Version 1.4.0" src="https://img.shields.io/badge/version-1.4.0-green.svg"/>
  <a href="https://nyu-acsys.github.io/raven/"><img alt="Project page" src="https://img.shields.io/badge/docs-nyu--acsys.github.io%2Fraven-blue.svg"/></a>
  <a href="https://raw.githubusercontent.com/nyu-acsys/raven/master/LICENSE"><img alt="MIT licensed" src="https://img.shields.io/badge/license-MIT-blue.svg"/></a>
  <a href="https://github.com/nyu-acsys/raven/actions/workflows/ci.yml"><img alt="Builds, tests &amp; co" src="https://github.com/nyu-acsys/raven/actions/workflows/ci.yml/badge.svg?branch=main"/></a>
</p>

Raven is an intermediate verification language and SMT-based deductive verifier based on concurrent separation logic. It is intended as an intermediate layer for building program verification tools that target concurrent programs. Raven can also be used as a standalone educational tool.

> **[nyu-acsys.github.io/raven](https://nyu-acsys.github.io/raven/)** — project page, with an introduction to the language and a [hands-on tutorial](https://nyu-acsys.github.io/raven/tutorial/). This file covers installing, running and developing Raven itself.

Raven's language design draws inspiration from projects like [Boogie](https://www.microsoft.com/en-us/research/project/boogie-an-intermediate-verification-language/), [Why3](https://www.why3.org/), and [Viper](https://www.pm.inf.ethz.ch/research/viper.html) but treats concurrency as a first-class citizen. 
Raven has a sizeable, and growing [collection](test/concurrent) of verified implementations of fine-grained concurrent data structures commonly found in the literature as well as real systems.

Raven supports features like *shareable* invariants, user-definable resource algebras ("monoids"), and a higher-order module system that enables code and proof reuse. Its inlined style of development, interleaving code and proof, streamlines the process of co-developing a program alongside its proof of correctness. The Raven verifier then translates Raven programs to verification conditions expressed in first-order logic, which are then automatically dispatched using the SMT solver [Z3](https://github.com/Z3Prover/z3).

Raven ships with a [library](lib/library/resource_algebra.rav) of standard resource algebra definitions, as well as higher-order resource algebra constructors that embody commonly occurring patterns in proofs of concurrent data structures. This helps the user get started with proofs quickly.

Raven's underlying meta-theory is based on the [Iris](https://iris-project.org/) separation logic framework. We simplify the Iris logic by carefully restricting its features (like higher-order quantification, impredicativity, and step-indexing). At the same time, we add complementary features like the higher-order module system to regain expressivity. The resulting logic is sufficiently expressive to verify complex concurrent algorithms, yet, amenable to robust SMT-based automation. The mechanization of Raven's program logic as an instance of the Iris framework is part of ongoing work.

## Contents
- [Portable Usage (via Docker)](#portable-usage-via-docker)
- [Installation](#installation)
- [Usage](#usage)
- [Examples](#examples)
- [Tutorial](#tutorial)
- [Extension API](#extension-api)
- [Development](#development)
- [Raven Verifier Manual](#raven-verifier-manual)
- [Scientific Background](#scientific-background)


## Portable Usage (via Docker):
We have made available a Docker image of Raven on DockerHub that can be directly executed without any installation, as follows:

```bash
$ docker run --rm ekanshdeepgupta/raven
Raven version 1.x.y
Verification successful.
```

This image comes pre-loaded with Raven's existing suite of examples. For example, we can run some existing examples:
```bash
$ docker run --rm ekanshdeepgupta/raven test/concurrent/lock/ticket-lock.rav
Raven version 1.x.y
Verification successful.

$ docker run --rm ekanshdeepgupta/raven test/ext/prophecy/lazy_coin.rav
Raven version 1.x.y
Verification successful.

$ docker run --rm  ekanshdeepgupta/raven test/ci/front-end/fail/tuple.rav
Raven version 1.x.y
[Error] File "test/ci/front-end/fail/tuple.rav", line 7, columns 20-22:
7 |     var zz: Int := x#2;
                        ^^
Type Error: Index out of bounds.
```

To examine these examples, we can run `cat` for example as follows:
```bash
$ docker run --rm --entrypoint cat ekanshdeepgupta/raven test/ci/front-end/bool_perm_ite.rav
field f: Int

proc p(x: Ref) {
    inhale !true ? true : own(x.f, 1, 1.0);
    exhale true ?  own(x.f, 1, 1.0) : true;
}
```
The complete suite of Raven's examples can be browsed at [test](./test) in this repository.

To run Raven on your own example files, say ./my/local/prog.rav, you can run:
```bash
$ docker run --rm -it -v $(pwd):/app/data -- ekanshdeepgupta/raven "/app/data/my/local/prog.rav"
```

To get our hands dirty, we can even access a shell inside the Docker image by executing:
```bash
$ docker run --rm -it --entrypoint /bin/bash ekanshdeepgupta/raven
/app# raven --shh test/ci/back-end/inhale_exhale.rav
Verification successful.

/app# ls /usr/local/bin
raven  z3
```


## Installation
To install Raven locally, it requires [`opam`](https://opam.ocaml.org/) (>= 2.1.0), OCaml (5.x; CI uses 5.1), and [Z3](https://github.com/Z3Prover/z3) (>= 4.13.0). Z3 is pulled in automatically as an opam dependency; if that build fails, consult the [`z3` opam package](https://opam.ocaml.org/packages/z3/) for its system-level prerequisites (a C++ toolchain and Python are typically needed). See [`dune-project`](dune-project) for the full list of OCaml library dependencies. Raven and all its dependencies other than `opam` can be installed by running the following sequence of commands.
```
$ git clone https://github.com/nyu-acsys/raven.git
$ cd ./raven
$ opam switch create raven 5.2.0
$ eval $(opam env)
$ opam install . --deps-only --with-test
$ dune build; dune install; dune runtest
```

A [Visual Studio Code extension](https://github.com/nyu-acsys/raven-lang) for IDE integration is also available.


## Usage
The Raven verifier can be executed on a file `test/concurrent/treiber_stack/treiber_stack_atomic.rav` as follows:
```
$ raven test/concurrent/treiber_stack/treiber_stack_atomic.rav
Raven version 1.x.y
Verification successful.
```
Here is a failing example:
```
$ raven test/ci/back-end/fail/fpu_fail.rav
Raven version 1.x.y
[Error] File "test/ci/back-end/fail/fpu_fail.rav", line 7, columns 2-14:
7 |   fpu(x.f, 4);
      ^^^^^^^^^^^^
Verification Error: This update may not be frame-preserving.
```


## Examples
Several examples of Raven programs can be found in the [test](test) folder. The [ci](test/ci) folder contains many small examples that can be used to learn Raven's syntax for specific features. Complete verified implementations of concurrent data structures can be found in the [concurrent](test/concurrent) folder. Here are a few notable ones to get started, in roughly increasing order of complexity:
1. [spin_lock](test/concurrent/lock/spin-lock.rav)
1. [monotonic_counter](test/concurrent/counter/counter_monotonic.rav)
1. [treiber_stack](test/concurrent/treiber_stack/treiber_stack_atomic.rav)
1. [atomic_resource_counter](test/comparison/arc_atomics.rav)
1. [give-up template](test/concurrent/templates/give-up.rav)
1. [bplustree](test/concurrent/templates/bplustree.rav)


## Tutorial
New to Raven? [**The Raven Tutorial**](https://nyu-acsys.github.io/raven/tutorial/) is a from-scratch, hands-on introduction — sequential Raven, ownership and resources, the module system, ghost code and basic concurrency, then a set of advanced capstones (fork/join, atomic contracts, iterated separating conjunctions). Every code listing in it is a real, checked `.rav` file. Its sources live in [docs/tutorial](docs/tutorial/); to browse it locally instead:
```bash
$ cd docs
$ npm install
$ npm run dev
```

## Extension API
Raven also comes with a modular extension API which is designed for front-end designers to be able to extend Raven's syntax directly, to get a custom IVL for their specific domain. They can implement Raven extensions to encode new front-end features, adding custom types, expressions, and commands to the IVL.
We provide extensive documentation along with a tutorial for this API at [docs/ext/README.md](docs/ext/README.md). We implement multiple different extensions and extensively document their code to demonstrate possibilities, and add several useful features to the language. At present, Raven comes with one optional extension which can be selected via the command-line flag `--extension`:
- ErrorCredits Extension (`eris`): This extension is available to prove error bounds for probablistic programs. Inspired from [Eris](https://dl.acm.org/doi/10.1145/3674635), we use this extension to verify a [collision-free hashmap](test/ext/error-credits/cf_hashmap.rav), and a [fault memory allocator](test/ext/error-credits/ec_dynamic_vec.rav). For example:
```bash
$ raven --extension eris test/ext/error-credits/ec_dynamic_vec.rav
Raven version 1.x.y
Verification successful.
```

Raven also comes with the Prophecy Extension, which implements _prophecy variables_. This is what plain `raven` (no `--extension` flag, i.e. `--extension default`) activates -- it has no flag of its own, and is mutually exclusive with the ErrorCredits extension above (combining the two is not sound), so it is not active under `--extension eris`. For example:
```bash
$ raven test/ext/prophecy/rdcss.rav
Raven version 1.x.y
Verification successful.
```


## Development
Raven's tests are [cram](https://dune.readthedocs.io/en/stable/tests.html) tests: each `.t` file under [`test`](test) runs `raven` on a sibling `.rav` file and diffs stdout against the recorded expected output.

To run a single test:
```bash
$ dune build @test/ci/back-end/agree_inhale        # runs test/ci/back-end/agree_inhale.t
```
If you've intentionally changed verifier output, accept the new output with:
```bash
$ dune promote
```
Other flags useful during development: `--typeonly` (type-check only), `--verbosity=debug` (also writes `front_end_processed_output.log`, the elaborated AST, and `log.smt2`, the SMT queries submitted to Z3, to the working directory).


## Raven Verifier Manual
Run `raven --help` for the full, authoritative option list. A few of the most commonly used flags:
- `--extension=VAL` (`default`, `eris`, or `prophecy`) — select a front-end extension.
- `--typeonly` — type-check the input without running verification.
- `--smt-timeout=VAL` (default `10000`) — timeout for the SMT solver, in ms.
- `--nostdlib` — skip loading the standard library.
- `--stats` — output only program stats (concrete/ghost instruction steps, number of specification formulae) instead of verifying.

## Scientific Background

For a detailed discussion of the motivation and theory behind Raven, including empirical evaluation, please refer to our paper:

> **Raven: An SMT-Based Concurrency Verifier** 
> Ekanshdeep Gupta, Nisarg Patel, and Thomas Wies.  
> *In Computer Aided Verification (CAV), 2025.* 
> **DOI:** [10.1007/978-3-031-98668-0_4](https://doi.org/10.1007/978-3-031-98668-0_4)
