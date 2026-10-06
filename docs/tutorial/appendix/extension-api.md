# Beyond This Tutorial: the Extension API

Everything in this tutorial is about writing *proofs* in Raven's existing language. A different,
more specialized audience instead wants to *extend* Raven's language itself, adding new types,
expressions, statements, and contract clauses without touching the core pipeline. This includes
people building a front-end verifier for their own language on top of Raven, or adding an
entirely new proof methodology.

That's what the **Extension API** is for. It is documented in `docs/ext/README.md` in the
repository, a much longer and more implementation-focused document than this tutorial. In short,
an extension is a higher-order OCaml module, parameterized over another extension, so extensions
can be stacked. `DefaultExt -> DecreasesExt -> AssertWithExt -> MatchExt` composes into
`RavenCore`, the language this entire tutorial has been using. `ProphecyExt` and
`ErrorCreditsExt` are two separate stacks, each built on top of `RavenCore` independently.
(Iris-style prophecy variables and Eris-style error credits for reasoning about probabilistic
programs aren't sound together, so they're never combined.) `ProphecyExt(RavenCore)` is what you
get by default, with no `--extension` flag, and `ErrorCreditsExt(RavenCore)` is selected with
`--extension eris`.

Each extension typically lives in its own directory under `lib/ext/`, with three parts: an
`.ml` module implementing the type-checking and rewrite-to-core logic for its new constructs, a
`_parser.mly` grammar fragment (merged into the main parser at build time, so all extensions'
syntax compiles into one parser), and optionally a `.rav` library of definitions loaded
alongside the standard library.

Note what is *not* on that list. New operations, including atomic hardware primitives, do not
need an extension at all. They are ordinary procedures, and {{ref app:hardware-primitives}} works through one from
scratch. The Extension API is for new **syntax**: a form of type, expression, statement, or
contract clause the parser does not have. Reach for it only once you have established that a
procedure will not do.

If you're the target audience for this appendix, the tutorial section of `docs/ext/README.md` is
the right place to continue, not this document.
