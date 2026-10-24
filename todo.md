24 oct, 2026:
- [x] Share the generic instances introduced by implemented interfaces when
    creating implicit module instances, as explicit instances already do:
    `Library.Seq.of_list(xs)` now accepts `xs: Library.List[Int]`.
- [x] Infer nested generic arguments when selecting overloaded functions:
    `F.get(b)` for `b: Box[Int]` fails with "No applicable overload" when
    `F[E]` declares both `get(b: Box[E])` and `get(b: Bool)`. This also affects
    unsealed functors; single-function inference handles the nested argument.
- [x] Place generated instances with mixed global and functor-local arguments in
    a scope where all arguments are visible: `Pair.first(e, true)` inside
    `Generic[E]`, with `e: E`, creates `Pair[E, Bool]` outside `Generic` and
    fails with "Unknown identifier Generic.E". This also affects unsealed functors.
- [x] Allow applying a nested functor through an instantiated outer module:
    `module OuterInt = Outer[Int]` followed by
    `module InnerBool = OuterInt.Inner[Bool]` reports "expects 0 arguments"
    even though `Outer[E]` declares `module Inner[F: Library.Type]`.
- [x] Match doubly nested generic types across sealed signatures:
    `get(b: Box[Box[E]])` in a sealed implementation fails to match the same
    declaration in its interface before any client call is checked.
- [x] Construct values of nested type aliases in generic instances without
    spurious nominal mismatches: with `Rose[E]` declaring `type Forest = List[T]`
    and `type NestedForest = List[Forest]`, assigning
    `List.::(forest, List.nil)` to `IntRose.NestedForest` reports two incompatible
    types both printed as `List[List[Rose.T]]`. Passing an existing value of the
    alias to a function works; investigate constructor instantiation inference.

23 oct, 2026:
- [ ] Make inhale/exhale fusion insensitive to contract conjunction grouping:
    normalize conjunctive assertions before matching resource transfers, preserving
    order, guards, source locations, and diagnostics. A fractional read with
    `requires own(x.contents, v, q) && q > 0.0` and
    `ensures own(x.contents, v, q) && r == v` currently fails to fuse, while
    separate clauses with adjacent ownership transfers fuse. Add a regression
    covering both forms; consider dependency-safe fusion across intervening pure
    assertions separately.
- [ ] Update the tutorial discussion of atomic operations and the Atomics library
    to use `atomic proc`.

21 oct, 2026:
- [x] The printer emits a fold, unfold, openInv or closeInv without witnesses
    with an empty witness list and trailing spaces, as `fold lseg(c, l)[]  ;`;
    it should print `fold lseg(c, l)`.
- [x] Expand generated aliases when emitting recursive datatype declarations:
    `type T = data { case node(v: Int, children: List[T]) }` refers to an alias
    introduced by instantiation. The datatypes are already grouped together;
    their fields must reference the datatype sorts before the aliases are declared.

20 oct, 2026:
- [ ] Infer implicit ghost arguments from invariants in the precondition: for
    `proc acquire(l: Ref, implicit ghost r: Ref) requires lock_inv(l, r)`, a
    caller holding `lock_inv(l, b)` gets an arbitrary `r` from `acquire(l)` and
    is told that the invariant is not in its mask; `acquire(l, b)` verifies.

17 oct, 2026:
- [x] Wire the VS Code plugin's `ravenServer.maxNumberOfProblems` into the protocol.
    The setting is unused so far, and its defaults disagree (100 in `package.json`,
    1000 in `server.ts`). Raven: honor an explicit `--max-errors` under `--lsp-mode`,
    which has no limit by default, and bump `lsp_protocol` to 4. Plugin: pass
    `--max-errors` from protocol 4 on, and show the "Stopped after N errors" note,
    which has no location.
- [ ] Recover from type errors per statement inside a callable body; a body stops at
    its first error.
- [x] Editor: report the verification status of each procedure and lemma (verified,
    failed, timed out) and show it in the plugin; add `--only <name>` and a "Verify
    this" code lens.
- [x] Editor: emit resolved symbols and their types for go to definition and hover
    with types; hovers should show which functor instance a name resolves to.
- [x] Editor: a document outline from the members, modules and named assertions that
    `--lsp-annotations` lists with their extents.
- [ ] Editor: inlay hints for what the verifier infers: implicit type arguments,
    masks, and whether a call is atomic.
- [x] Editor: show counterexamples for failed assertions from Z3's model, mapped back
    through lowering and SSA.
- [x] Counterexamples: show which branches the failing path took, e.g. as inlay hints
    at each `if` on the path.
- [x] Map literals with a default, such as `{1 := 5, else 4}`, as counterexamples show
    maps.
- [x] Incremental verification: re-check only members whose dependencies changed
    since the last run.
- [ ] Editor: a "Show elaborated program" command that opens the elaborated or
    lowered program read-only; needs a flag that prints it to stdout.
- [ ] Plugin: snippets for procedures, lemmas, loops with invariants, and module and
    interface skeletons.

15 oct, 2026:
- [x] Generative functor instances with type arguments: in `G[Int]`,
    `Seq[E]` does not match `Seq[Int]` (independent of interfaces).
- [x] Investigate expressing error messages only in source-level terms: type errors
    currently expose internally generated modules, e.g. `GI.GenInst$$Seq$$G_E_T.T`
    instead of `Seq[E]`/`Seq[Int]`, and `TypeMod$$...` rep modules.
- [x] Support `==` on `Seq`.
- [ ] Finish the limited-functions branch.
- [ ] Add explicit triggers to the remaining (~500) untriggered user quantifiers.
- [ ] Investigate solver flakiness under parallel `dune runtest`
    (`dist_counter`, `ticket_lock_atomic*`, `amortised_hash`); consider a solver
    option `smt.arith.nl.delay=200`.
- [x] Consider moving from exception-based to monadic error handling; then move
    the global warning/annotation refs into the monad's state and remove the
    second `try ... with` in `ExprTyping.set_checked_type`.
- [x] Look up unqualified destructors in the receiver's data type: `l.hd` on
    `l: Library.List[E]` fails with "Unknown identifier hd" unless `hd` is in scope.
- [x] Infer a functor argument that occurs only inside another instance: with
    `G[E]` taking a `Box[E]`, `G.first(b)` for `b: Box[Int]` fails with
    "Cannot unify type Box[G.E] with type Box[Int]", while an explicit
    `module GI = G[Int]` works.
- [x] Applying a user-defined functor to one of its own instances, as in
    `Box[Box[Int]]`, fails with "Unknown identifier Box.TypeMod$$...". Inside a functor
    `G[E]`, `Box[Box[E]]` is then not shared by `G[Int]` with `Box[Box[Int]]`.
- [x] Don't record editor annotations for generated modules: hovering over `Seq[Int]`
    shows the inherited member `free val default: T` of the module that wraps `Int`.

30 jul, 2026:
- [x] Consider warning when an explicitly named import (`import M.x`) is
    hidden by a declaration of `x` in the importing module. Local declarations
    intentionally take precedence regardless of declaration order, hiding the
    entire imported overload group. Keep this behavior; exclude wildcard
    imports from the warning, since their shadowing is common and intentional.

16 nov, 2024:
- [x] fix ident sanitization bug identified by Lucas.
- [x] move statistics counting to after type-checking for greater accuracy.

22 oct, 2024:
- [x] fix bug with existenials occuring in other variables' skolem function
    + [x] rewrite the entire elim_a functionality.
    + [x] fix issue with order of adding vs typechecking of mutually dependent skolems
- [x] add another assertion for ISC that quantifies over the actual value, not just location
- [x] exhale order of clause witness computation bug

- [x] formalize masks
- [x] introduce fold existential witness notation

- [x] move injectivity check outside.
- [x] Share ISC inverse functions and injectivity lemmas across predicate fold/unfold expansions via the source-level ISC cache
- [x] sweep to add default triggers for every Quant
    + [x] fix missing triggers in all `Expr.mk_binder` calls

- [x] add forks
- [x] toy around with preds as macros



Type-checking:
  - [x] Ensure that return variables are not allowed in pre-conditions
  - [x] Check argument counts and types for `openAU` and `commitAU`
  - [x] Check that assertions have type `Perm` (including `Bool`) and ternary conditions have type `Bool`
  - [x] Ensure that return variables of functions are not used in the function body
  - [x] Forbid implicit predicate input parameters; implicit parameters must follow `;`
  - [x] Check that `bindAU` assigns to exactly one ghost token of the enclosing procedure's token type

- [x] Implement mask computation to check interface <-> module compatibility
- [x] Revamp witness computation code

- [x] Fix `return proc()` stmts
- [x] Allow parsing of `map[m1][m2]` expressions
    (Thomas did implement a fix for this, but needs review)

- [x] Remove obsolete built-in CAS/FAA/XCHG AST definitions and the commented CAS grammar
- [x] Correct the FPU arity diagnostic to describe both location and reference/field forms
- [x] Allow types to be used as modules implementing Library.Type



===

- [x] Fix dependency analysis wrt auto lemmas
- [x] Investigate spurious "unknown"s in the middle of log files
