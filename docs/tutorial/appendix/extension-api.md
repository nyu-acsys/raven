# Appendix C: Beyond This Tutorial — the Extension API

Everything in this tutorial is about writing *proofs against* Raven's existing language. A
different, more specialized audience — people building a front-end verifier for their own
language on top of Raven, or adding an entirely new proof methodology — instead wants to
*extend* Raven's language itself: new types, new expressions, new statements, new contract
clauses, without touching the core pipeline.

That's what the **Extension API** (`docs/ext/README.md` in the repository, a much longer and more
implementation-focused document than this tutorial) is for. The short version: an extension is a
higher-order OCaml module, parameterized over another extension, so they stack —
`DefaultExt -> ListExt -> AtomicExt -> DecreasesExt` composes into `RavenCore`, the language this
entire tutorial has been using. `ProphecyExt` and `ErrorCreditsExt` are two separate stacks built
on top of `RavenCore` independently (Iris-style prophecy variables and Eris-style error credits
for reasoning about probabilistic programs aren't sound together, so they're never combined);
`ProphecyExt(RavenCore)` is what you get by default, with no `--extension` flag, and
`ErrorCreditsExt(RavenCore)` is selected with `--extension eris`.

Each extension typically lives in its own directory under `lib/ext/`, with three parts: an
`.ml` module implementing the type-checking and rewrite-to-core logic for its new constructs, a
`_parser.mly` grammar fragment (merged into the main parser at build time, so all extensions'
syntax compiles into one parser), and optionally a `.rav` library of definitions loaded
alongside the standard library. If you're the target audience for this appendix,
`docs/ext/README.md`'s tutorial section is the right next stop, not this document.
