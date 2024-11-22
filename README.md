# Raven
![Version 1.0](https://img.shields.io/badge/version-1.0-green.svg)
[![MIT licensed](https://img.shields.io/badge/license-MIT-blue.svg)](https://raw.githubusercontent.com/nyu-acsys/raven/master/LICENSE)
[![Builds, tests & co](https://github.com/nyu-acsys/raven/actions/workflows/ci.yml/badge.svg?branch=dev)](https://github.com/nyu-acsys/raven/actions/workflows/ci.yml)

<img align="right" width="150" src="logo.png"/>

Raven (Resource Algebra Verification ENgine) is an SMT-based deductive verifier for concurrent separation logic. Raven supports features like invariants, custom user-defined resource algebras ("monoids"), and a powerful higher-order module system that enables code and proof re-use. Raven also has smart heuristics that automate many low-level details, and an inlined style of development that interleaves code and proof. This streamlines the process of co-developing a program alongside its proof of correctness.

Raven provides a highly-automated, user-friendly front-end that draws heavily from projects like [Dafny](https://github.com/dafny-lang/dafny) and [Viper](https://www.pm.inf.ethz.ch/research/viper.html). Raven has a sizeable, and growing [collection](test/concurrent) of verified implementations of fine-grained concurrent data structures commonly found in the literature and as well as real systems.

These implementations are then translated to first-order logic and passed to the [Z3](https://github.com/Z3Prover/z3) SMT-solver to determine whether the user-provided input verifies successfully.

Raven also ships with a [library](lib/library/resource_algebra.rav) of standard resource algebra implementations, as well as higher-order resource algebra constructors that embody commonly occuring patterns in proofs of concurrent data structures. This helps the user get started with proofs quickly.

Raven's underlying separation logic is based on the [Iris](https://iris-project.org/) separation logic framework. We vastly simplify the Iris logic by carefully restricting its most higher-order features (like impredicativity and step-indexing). This results in a sufficiently expressive logic that is amenable to robust SMT-based automation. Developing a formal proof of Raven's compatibility with Iris is part of ongoing-work.

## Installation
Raven can be installed by running the following sequence of commmands. It requires [opam](https://opam.ocaml.org/).
```
$ git clone https://github.com/nyu-acsys/raven.git
$ cd ./raven
$ opam switch create raven 5.2.0
$ opam switch raven
$ opam install . --deps
$ dune build; dune install; dune runtest
```

## Examples
Several examples can be found in the [test](test) folder. The [ci](test/ci) folder contains many small example that can be used to learn Raven syntax for specific features. Complete verified implementations of concurrent data structures can be found in the [concurrent](test/concurrent) folder. Here are a few notable ones to get started, in roughly increasing order of complexity:
1. [spin_lock](test/concurrent/lock/spin-lock.rav)
1. [monotonic_counter](test/concurrent/counter/counter_monotonic.rav)
1. [treiber_stack](test/concurrent/treiber_stack/treiber_stack_atomics.rav)
1. [atomic_resource_counter](test/comparison/arc_atomics.rav)
1. [bplustree](test/concurrent/templates/bplustree.rav)
1. [give-up template](test/concurrent/templates/give-up.rav)

## Usage
Raven can be executed on a file `test/concurrent/treiber_stack/treiber_stack_atomics.rav` as follows:
```
$ raven test/concurrent/treiber_stack/treiber_stack_atomics.rav
Raven version 1.0
Verification successful.
```
Here is a failing example:
```
$ raven test/ci/back-end/fail/fpu_fail.rav
Raven version 1.
[Error] File "test/ci/back-end/fail/fpu_fail.rav", line 7, columns 2-14:
7 |   fpu(x.f, 4);
      ^^^^^^^^^^^^
Verification Error: This update may not be frame-preserving.
```

### Raven Manual
```
RAVEN(1)                         Raven Manual                         RAVEN(1)

NAME
       raven

SYNOPSIS
       raven [OPTION]… [INPUT]…

ARGUMENTS
       INPUT
           Input file.

OPTIONS
       --color=WHEN (absent=auto)
           Colorize the output. WHEN must be one of auto, always or never.

       --lsp-mode
           Format error messages for LSP integration.

       --nostdlib
           Skip standard library.

       -q, --quiet
           Be quiet. Takes over -v and --verbosity.

       --shh
           Suppress greeting.

       --smt-info
           Let Z3 produce diagostic output.

       --smt-timeout=VAL (absent=10000)
           Timeout for SMT solver in ms.

       --stats
           Output only program stats: concrete instruction steps, ghost
           instruction steps, and number of specification formulae

       --typeonly
           Only type-check input program but do not verify it.

       -v, --verbose
           Increase verbosity. Repeatable, but more than twice does not bring
           more.

       --verbosity=LEVEL (absent=warning)
           Be more or less verbose. LEVEL must be one of quiet, error,
           warning, info or debug. Takes over -v.

COMMON OPTIONS
       --help[=FMT] (default=auto)
           Show this help in format FMT. The value FMT must be one of auto,
           pager, groff or plain. With auto, the format is pager or plain
           whenever the TERM env var is dumb or undefined.

       --version
           Show version information.
```