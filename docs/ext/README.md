# Raven's Extension API

This file contains a thorough documentation of Raven's Extension API. It is intended as a starting point for a verification expert developing a front-end verification tool, hereafter referred to as the _programmer_, to be able to add their own features to Raven by implementing their own extensions. For this purpose, not only does this document describe the API in detail, it also contains pointers to parts of several OCaml code files where relevant Raven functionality is implemented.


## Overview

Raven's Extension API is designed to allow a programmer to rapidly adapt Raven's front-end language for specific use-cases, without much familiarity with Raven's entire existing pipeline. The programmer can define custom types, expressions, statements, and contract clauses that they want to add to Raven.

We make use of OCaml's extensible variant types to expose types to the programmer which tie into the core AST representations for Raven's types, expressions, statements, and contracts. These types are `AstDef.Type.type_ext`, `AstDef.Expr.expr_ext`, `AstDef.Stmt.stmt_ext`, and `AstDef.Stmt.contract_ext` defined in `lib/ast/astDef.ml`, which allow the programmer to extend types, expressions, statements, and callable/loop contracts respectively.

`type_ext`/`expr_ext` share one shape: a new constructor is embedded in an existing AST node (`Type.App (TypeExt ..., args, attr)`, `Expr.App (ExprExt ..., args, attr)`) alongside a generic `expr list` of arguments, and the extension's job is to type-check and then *rewrite that one node* into simpler, "native" Raven constructs. `Stmt.stmt_ext` (the single OCaml extensible type) backs *two* different extension points, because a `basic_stmt_desc` (the kind of statement that can never contain nested statements of its own -- an assignment, a `fold`/`unfold`, a `havoc`, etc.) has no case for embedding a nested `Stmt.t`:

- `Stmt.basic_stmt_desc`'s `BasicStmtExt of (stmt_ext * expr list)` case follows the same flat `(tag, expr list)` shape as `type_ext`/`expr_ext` above, for a custom statement that's just an argument list -- e.g. `AtomicExt`'s `cas(...)`/`faa(...)`.
- `Stmt.stmt_desc`'s `StmtExt of stmt_ext` case (a sibling of `Block`/`Basic`/`Loop`/`Cond`, not nested inside `Basic`) is self-contained: your constructor carries whatever payload it needs directly, including a nested `Stmt.t` if your construct needs one -- e.g. `AssertWithExt`'s `assert e with { ... }`, whose payload includes the whole proof block. See [Statement-bodied extensions](#statement-bodied-extensions-stmtext-at-the-stmt_desc-level) below.

Both cases live in the same `type Stmt.stmt_ext = ..`, and the `ExtApi.Ext` API accordingly has two parallel families of hooks for them (`..._basic_stmt_ext_...`/`type_check_basic_stmt`/`rewrite_basic_stmt_ext` for the first, `..._stmt_ext_...`/`type_check_stmt_ext`/`rewrite_stmt_ext` for the second) -- pick whichever shape fits your construct; nothing stops a single extension from declaring constructors of both kinds.

`contract_ext` is structurally different again: `Callable.call_decl` and `Stmt.loop_desc` each carry a plain `Stmt.contract_ext list` (`call_decl_contract_ext`/`loop_contract_ext`), and each list entry is a self-contained value -- the extension's constructor carries whatever payload it needs directly, the same self-contained shape as the `stmt_desc`-level `StmtExt` above, just attached to a callable/loop rather than embedded as a statement.

To make an extension, broadly speaking, the programmer needs to implement a module satisfying the `ExtApi.Ext` API. These modules have a signature like so:
```
module SampleExt (Cont: ExtApi.Ext) : ExtApi.Ext
```

These are higher-order modules that accept, as a parameter, another extension module implementing the `ExtApi.Ext` interface. This allows us to "stack" these extensions on top of each other, and conveniently adjust the exact set of features we want to support when we compile Raven. This happens in `lib/ext/ext.ml`.

`ExtApi.Ext` is a large signature -- dozens of `val`s across [AstDef](#astdef)/[Rewriter](#rewriter)/[Typing](#typing)/[Rewrites](#rewrites)/[Contracts](#contracts) -- but a typical extension only cares about a handful of them; the rest should just do whatever `Cont` (the rest of the chain) would have done anyway. Since `Cont` is itself a first-class module already satisfying `ExtApi.Ext`, the way to get that "do what `Cont` does" behavior for free, for every hook you don't otherwise mention, is to open your module with `include Cont`:

```ocaml
module MyExt (Cont : ExtApi.Ext) = struct
  include Cont   (* every hook defaults to Cont's, no line needed per hook *)

  type Stmt.contract_ext += MyClause of Stmt.spec list

  (* Only the handful of hooks MyExt actually cares about need a definition below;
     everything else -- pr_stmt_ext, type_check_expr, rewrite_type_ext, the other
     three contract_ext hooks, etc. -- is already covered by `include Cont` above. *)
  let contract_ext_is_recognized = function
    | MyClause _ -> true
    | other -> Cont.contract_ext_is_recognized other
  let type_check_contract_ext = ...
  ...
end
```

This is the pattern every extension in `lib/ext/` uses; when a new hook is added to `ExtApi.Ext` in the future, only the extensions that actually need to do something for it have to change -- every other extension keeps compiling unmodified, since `include Cont` picks up the new hook's default automatically. The one thing this can silently get wrong if you're not careful: `include Cont` also pulls in `Cont.lib_source`/`lib_sources`, but every extension needs its *own* `lib_source` (or `None`) and must still explicitly define `lib_sources` as `(Option.to_list lib_source) @ Cont.lib_sources` (see [Epilogue](#epilogue)) -- if you skip that and just let `include Cont` supply `lib_sources`, your own library file silently never gets compiled in.


## Using Current Extensions

We have added two new extensions, Prophecy extension and ErrorCredits extension. These are mutually exclusive -- combining Iris-style prophecy variables with Eris-style error credits is not sound, so the two are never stacked together. Prophecy is what `default` (no `--extension` flag at all) means; ErrorCredits is selected instead via `--extension eris`. The `--extension` command-line flag takes one of two values: `default | eris`. For example:

```
$ raven test/ext/prophecy/clairvoyant_coin.rav
$ raven --extension eris test/ext/error-credits/ec_examples.rav
```

There are also a Decreases extension, an AssertWith extension and a Match extension, all described below; unlike Prophecy and ErrorCredits, each is stacked into *both* `--extension` choices unconditionally (see [`ext.ml`](../../lib/ext/ext.ml)) rather than being one more mutually-exclusive value the flag can take.

### Decreases Extension

We implement this extension (`lib/ext/decreasesExt/`) to check termination of recursive `func`s, `proc`s, `lemma`s, and `while` loops, via a `decreases` contract clause. It is the reference implementation of a `contract_ext`-based extension -- see [Contracts](#contracts) below for how the API it uses works in general.

`decreases e1, ..., en` declares a termination measure: a lexicographic tuple of expressions over the callable's own parameters (or, on a loop, over its loop variables), each required to be of a type with a `Library.WellFoundedOrder` instance -- resolved from the expression's own type, not fixed to `Int` (see `lib/ext/decreasesExt/well_founded_order.rav`, this extension's own library file, for the shipped instances: `IntOrder`, `Ordinal`, `LexOrder`, `MultisetOrder`, `SetOrder`). A self-recursive `data` type doesn't need one hand-written: if no `WellFoundedOrder`-implementing wrapper is in scope for it, a structural order is auto-generated on demand instead (a flat, non-recursive `lt` built directly from the type's own constructors -- `x` decreases `y` iff `x` equals one of the self-recursive fields of whichever variant `y` was built with), *trusted* rather than proven well-founded, the same meta-theoretic fact `OrdinalBase`'s own well-foundedness already rests on (see that module's doc comment), just applied directly instead of via an embedding proof. This only covers straightforward self-recursion: a type parameter (e.g. `Library.List[E]`'s `E`) or a field of a *different* `data` type (including one that's part of a mutually-recursive cycle back to this one) is never treated as a decreasing position, so a measure that genuinely needs either still requires a hand-written instance. The extension inserts an assertion before every recursive call that the measure computed from the call's actual arguments is lexicographically smaller, according to that instance's `lt`, than the measure at the callable's current parameter values -- for `proc`/`lemma`, this happens directly in the callable's own body; for `func`, it piggybacks on the auto-generated contract-checking lemma (`Rewrites.rewrite_add_func_contract_lemmas`), since a `func` body is a pure expression with no statements of its own to instrument. A `while` loop's `decreases` clause is desugared for free: `Rewrites.rewrite_loops` already turns every loop into a self-recursive tail-call procedure, so once its `decreases` clause is transferred onto that procedure's contract, no separate loop-specific logic is needed.

Checking is opt-in per callable: a recursive callable with no `decreases` clause is left completely unchecked, exactly as if this extension didn't exist. Mutual recursion is supported, not just literal self-calls: a call between two *different* callables is instrumented whenever they lie in the same strongly-connected component of the module's call graph, and every member of such a group must declare a `decreases` clause of the same lexicographic arity using the same `WellFoundedOrder` instance at each position (a group where some members declare one and others don't, or use incompatible instances, is a type error rather than silently under-checked).

```
func fac(n: Int)
  returns (res: Int)
  requires n >= 0
  ensures res >= 1
  decreases n
{
  n > 0 ? n * fac(n-1) : 1
}
```

### AssertWith Extension

We implement this extension (`lib/ext/assertWithExt/`) for `assert e with { proof }`, Raven's natural-deduction-style construct for proving a fact `e` via an auxiliary ghost proof block that is checked in isolation and then discarded, so the proof's scratch work never pollutes the surrounding SMT state. It is the reference implementation of a `stmt_desc`-level, statement-bodied `stmt_ext` extension -- see [Statement-bodied extensions](#statement-bodied-extensions-stmtext-at-the-stmt_desc-level) below for how the API it uses works in general.

`e` may be a bare fact, or headed by `forall`/`exists`:
- For a bare fact or a `forall`-headed goal, the proof block is checked once against a truly arbitrary instance (the `forall`'s bound variables are `const` throughout the proof, so it cannot pin them to a specific witness and then illegitimately generalize), then discarded, and only `assume e` survives.
- For an `exists`-headed goal, the bound variables stay mutable, and the proof is expected to establish a concrete witness (typically via assignment) -- ordinary existential introduction, which needs no generalization step.

Soundness of "prove once, discard the proof, keep only the conclusion" depends on `e` being *pure* (no `own`/predicate/atomic-update content): the goal is type-checked against `Type.bool` rather than the wider `Type.perm` ordinary `assert`/`assume` specs accept, since `assume`ing an impure fact for free -- with nothing on the surviving path having paid for whatever resource the discarded proof consumed -- would conjure that resource out of nothing.

```
proc example()
{
  assert forall x: Int :: x * x >= 0 with {
    // ... proof steps here, isolated from the rest of the callable's SMT state ...
  }
}
```

### Match Extension

We implement this extension (`lib/ext/matchExt/`) for working with `data` types: the constructor test `x is cons`, and `match` expressions. It is the reference implementation of an extension construct that *binds variables* -- see [Constructs that bind variables](#constructs-that-bind-variables-disambiguate_expr_ext) below for how the API it uses works in general.

`x is cons` is a `Bool` saying whether `x` was built with the `cons` constructor. The constructor name is deliberately unqualified -- no `MyType.cons` prefix -- and is resolved against `x`'s own already-known type, exactly the way plain field access (`x.elem`) already resolves a destructor. It lowers to the reconstruct-and-compare idiom `x == cons(x.elem, x.tl)`, which Z3's native datatype theory reasons about directly, so it costs about what a native tester would.

`match` selects per constructor, binding each arm's pattern variables to the corresponding fields:

```
type IntList = data {
  case nil;
  case cons(elem: Int, tl: IntList)
}

func sum_hd(xs: IntList) returns (r: Int) {
  match xs {
    case nil => 0
    case cons(e, t) => e
  }
}
```

Arms are checked for exhaustiveness against the scrutinee's type: absent a wildcard arm, every constructor must be named exactly once. A wildcard arm (`case _ => ...`) stands in for the rest and must come last. A pattern variable may also be written `_`, which binds nothing and may repeat within an arm. This is a plain comparison against the symbol table's record of the type's constructors -- an ordinary type error, checked locally with no SMT call. A `match` lowers to a right-nested `Ite` chain guarded by the same recognizer condition `is` uses, with no guard needed on the final arm, since exhaustiveness already establishes it is the only one that can apply.

Both forms also work on the stdlib `Library.List[T]`, an ordinary generic module instantiation whose underlying `data` type `as_data_type` reaches the same way it reaches any module's rep type; an *extension-provided* type (one still tagged with its own `Type.type_ext`, not yet resolved to whatever it elaborates to) gets one extra step first, generically, so any such type backed by a `data` type gets the same treatment (see `MatchExt.as_data_type`).

`is` binds at exactly the level `==`/`!=` do -- tighter than `&&`/`||`/`==>`, looser than arithmetic -- so it composes into a larger formula without parentheses (`a is cons && b is cons`). It is non-associative with `==`, so `a == b is c` is a syntax error rather than an arbitrary grouping. Reaching that level from an extension's parser fragment is what `rel_expr`/`eq_expr` being `%public` in core `parser.mly` is for; see [Constructs that bind variables](#constructs-that-bind-variables-disambiguate_expr_ext) for the other core hook this extension drove.

Pattern variables may be named after the fields they bind (`case cons(elem, tl) => ...` for `cons(elem: Int, tl: T)`) without shadowing those destructors for the rest of the callable -- the natural spelling is the safe one.

### ErrorCredits Extension (`eris`)
We implement this extension to add support for reasoning about Error-credits, and probablistic programs. This extension can be enabled with the:
  `--extension eris`
command-line argument.

This extension introduces:
  - `ErrorCreds` expression: these represent error credit resources
  - `lhs := EC.rand(n);` command: to generate a random number between `0` and `n-1`
  - `lhs := EC.rand(n; ECVal: !=k);` command: to generate a random number between `0` and `n-1`; then it spends enough error credits and ensures that the generated number is not equal to `k`
  - `lhs := EC.rand(n; ECFn: EC.error(e), \x :: body(x));` command: to generate a random number between `0` and `n-1`; then it redistrbutes `e` error credits according to the function defined by `\x :: body(x)`.
  - `lhs := EC.rand(n; ECList: !in ls);` command: to generate a random number between `0` and `n-1`; then it spends enough error credits and ensures that the generated number is not in the list `ls`.
  - `EC.contra()` command: to abort the proof when we get ownership of `EC.error(1.0)`.

This extension is available to prove error bounds for probablistic programs. Inspired from [Eris](https://dl.acm.org/doi/10.1145/3674635), we use this extension to verify a [collision-free hashmap](test/ext/error-credits/cf_hashmap.rav), and a [fault memory allocator](test/ext/error-credits/ec_dynamic_vec.rav). For example:
```bash
$ raven --extension eris test/ext/error-credits/ec_dynamic_vec.rav
Raven version 1.x.y
Verification successful.
```

### Prophecy Extension
We implement this extension to add support for Iris-style prophecy variables. This extension is what `--extension default` (equivalently, no `--extension` flag at all) activates -- it requires no flag of its own. It is mutually exclusive with the ErrorCredits extension below (combining the two is not sound), so it is *not* active under `--extension eris`.

A prophecy variable denotes a value (or sequence of values) that will only be 
observed at a future point during program execution. In particular, the value
may depend on non-deterministic choices (such as scheduler decisions) that will
be made between the current point of execution and the point when the value 
will be observed. A prophecy variable allows one effectively to predict the 
outcome of such future choices and reason about them before they occur 
(e.g., via case analysis).

The extension implements:
  - a new parametric type `Proph[T]` whose values represent prophecies p predicting values of type T, 
  - a command `proph_id, proph_val := Proph.new[T];` for creating new sequence prophecies.
  - a command `proph_id, proph_val := Proph.new_1[T];` for creating new one-shot prophecies
  - a command `Proph.resolve(proph_id, value);` for resolving prophecies.

For example:
```bash
$ raven test/ext/prophecy/rdcss.rav
Raven version 1.x.y
Verification successful.
```

## Creating a New Extension

An extension typically consists of 3 files, and may contain a 4th file. For a new extension say `SampleExt`, these files are:

1. `sampleExt.ml`: This file contains the `SampleExt` module that satisfies the `ExtApi.Ext` API. This contains, at a high level, the declarations of the additional AST constructs, along with functions to type-check these constructs, as well as _rewrite_ these constructs into simpler Raven terms.

2. `sampleExt_parser.mly`: This file contains the parser rules for the new syntax that the extension needs. These rules are then combined with Raven's existing parser and compiled by Menhir. Raven's parser makes certain non-terminals public, which means they can be referenced from outside files. These terminals can then be extended using other public terminals, and other freshly defined tokens.

3. `dune`: This file is for the `dune` build system. It defines the current module along with dependencies so that the `dune` build system can compile the code. This file declares the name of the module, ensure that it is equal to `SampleExt`. 

4. (Optional) `sampleExt_lib.rav`: This file contains optional Raven code with Raven declarations relevant for implementing the extension. This file is included as part of Raven's standard library when compiling Raven. This allows the programmer to include certain Raven definitions for modules, interfaces, procedures, functions, types, etc that can then be used for example during the rewriting process in `sampleExt.ml`.

The best way to get started with a new extension is to copy an existing extension and clear out the existing functionality. There is also the `blank_ext.ml.md` file provided in the `ext` folder to serve as a quick-start for new extensions.


## Activating a New Extension

Once the programmer has created the extension such that it successfully compiles with the `dune build` command, they must complete the following steps to make sure the extension is integrated into the Raven pipeline and becomes usable:

1. In [lib/ext/dune](../../lib/ext/dune): 
  add the extension as a dependency by appending `sampleExt` to the `libraries` field of the `library` stanza (line 3).

2. In [lib/frontend/dune](../../lib/frontend/dune):
  a. add the extension as a dependency by appending `sampleExt` to the `libraries` field of the `library` stanza (line 3).

  b. add a rule to copy the `sampleExt_parser.mly` file into the `lib/frontend` directory. Like this:
  ```dune
    (rule
    (target sampleExt_parser.mly)
    (deps ../ext/sampleExt/sampleExt_parser.mly)
    (action (copy %{deps} %{target})))
  ```

  c. append `sampleExt_parser` to the `modules` field of the `menhir` stanza.

3. In [lib/frontend/terminals.ml](../../lib/frontend/terminals.ml), add any new keywords required by the extension. These correspond to the new tokens declared in `sampleExt_parser.mly`.

4. Finally, in [lib/ext/ext.ml](../../lib/ext/ext.ml):
  a. add a new module `SampleExtInstance` that instantiates `SampleExt` with an existing extension and introduce it into the chain of extensions. Typically, newer extensions should be added towards the end as the "outermost" instantiations.
  b. add an entry for it to `module_map`, the function that resolves a `supported_extensions` value (in turn parsed from the `--extension` command-line flag) to the corresponding `(module ExtApi.Ext)`.

  Not every extension needs to be one more `--extension` choice, though: `DecreasesExt` (see [Decreases Extension](#decreases-extension)) is instead stacked directly into the base of the chain, so it's present under every `--extension` value rather than being mutually exclusive with the others. Do this if your extension's functionality is orthogonal to which of the existing extensions is active, by inserting your `<Ext>Instance` earlier in the chain (as `Cont` for the modules built on top of it) instead of adding it to `module_map`.

5. That's the only place the new extension needs to be registered: [raven.ml](../../bin/raven.ml)'s `main` resolves the `--extension` flag via `Ext.module_map` and passes the result down through the rest of the pipeline automatically (see [Wiring: how `ext_hooks` reaches your code](#wiring-how-ext_hooks-reaches-your-code) below).

6. Run `dune build; dune install` to compile Raven with the new extension.

That's it! 
- With the updated parser, Raven front-end will support the newly defined syntax.
- With the definition of the `Ext` module updated, Raven utilizes the new extension constructs while processing the input program.


## ExtApi - The extension API

In this section we describe the API that the programmer must implement in order to build an extension.

Any module for an extension implementing the API starts with declarations introducing new branches for some or all of `Type.type_ext`, `Expr.expr_ext`, `Stmt.stmt_ext`, or `Stmt.contract_ext` types, thereby extending Raven's syntax by introducing new types, expressions, statements, and contract clauses, respectively.

As a running example for `type_ext`/`expr_ext`/`stmt_ext`, let us consider that we want to add a new statement `randEven(n)` which denotes randomly sampling an _even_ number from 0 to n-1. This is a `basic_stmt_desc`-level (flat, `expr list`-only) statement -- see [Statement-bodied extensions](#statement-bodied-extensions-stmtext-at-the-stmt_desc-level) below instead if your construct needs to carry a nested `Stmt.t` of its own, e.g. a proof block.

So, one would introduce a new kind of statement as follows:

```
type Stmt.stmt_ext +=
  | RandEven
```

This constructor directly extends Raven's AST with a new statement type. Note that we do not indicate any arguments for the new statement. In Raven, each statement is combined with an expression array of arguments.

While developing the extension, the general principle is that whenever an extension matches on the corresponding types `type_ext`, `expr_ext`, `stmt_ext`, or `contract_ext`, it should handle all the cases of the constructor that are defined in this file, and include a catch-all case which calls the corresponding functionality from the `Cont` module. Here is an example:

```ocaml
  let basic_stmt_ext_symbols stmt_ext =
    match stmt_ext with
    | RandEven -> 
      (* Handle the RandEven case *)
      Set.empty (module QualIdent)
    | _ -> 
      (* Defer to the continuation for any other case *)
      Cont.basic_stmt_ext_symbols stmt_ext
```

This, combined with the "chain" in which we instantiate these modules, means that each extension constructor gets handled by the right extension.

The API comprises of the following sections.

### Config

These values are used to configure certain options for your extension.

- `val lib_source : (string * string) option`
This value can optionally contain a Raven library file, such as `sampleExt_lib.rav` to be included as part of the current extension. If no such library is required, the programmer can set this to `None`. In order to include `sampleExt_lib.rav` for instance, set it as follows:

`let lib_source = Some ("sampleExt_lib.rav", [%blob "sampleExt_lib.rav"])`, and make the following modifications to the `dune` file located in the extension:
a. add `ppx_blob` in the `pps` list in the `preprocess` option of the `library` stanza.
b. add `(preprocessor_deps (file sampleExt_lib.rav))` to the `library` stanza. 

Please take a look at [sampleExt.ml](../../lib/ext/sampleExt/sampleExt.ml) and [dune](../../lib/ext/sampleExt/dune) for an example of how to include an optional library file.

If your extension needs its own local variables to reliably encode new constructs during rewriting (e.g. a scratch ghost local), don't reach for a config value here -- there isn't one, on purpose. See `rewrite_callable_entry` under [Rewrites](#rewrites): it lets you introduce (via `Rewriter.introduce_symbol`) and initialize whatever locals a specific callable needs, sized/typed/named however that callable requires, rather than a fixed set added uniformly (and mostly unused) to every callable in the program.

### AstDef

The API contains the following functions in the AstDef section:

```ocaml
  val type_ext_to_name : (Type.type_ext -> string)

  val expr_ext_to_string : (Expr.expr_ext -> string)

  val pr_basic_stmt_ext : Stdlib.Format.formatter -> Stmt.stmt_ext -> expr list -> unit
  val contract_ext_to_string : Stmt.contract_ext -> string

  val basic_stmt_ext_symbols: Stmt.stmt_ext -> QualIdentSet.t
  val basic_stmt_ext_local_vars_modified : Stmt.stmt_ext -> expr list -> ident list
  val basic_stmt_ext_fields_accessed : Stmt.stmt_ext -> expr list -> qual_ident list

  val pr_stmt_ext : Stdlib.Format.formatter -> Stmt.stmt_ext -> unit
  val stmt_ext_symbols : Stmt.stmt_ext -> QualIdentSet.t
  val stmt_ext_local_vars_modified : Stmt.stmt_ext -> ident list
  val stmt_ext_fields_accessed : Stmt.stmt_ext -> qual_ident list

  val stmt_ext_atomicity : Stmt.stmt_ext -> Stmt.stmt_atomicity

  val type_ext_is_recognized : Type.type_ext -> bool
  val expr_ext_is_recognized : Expr.expr_ext -> bool
  val stmt_ext_is_recognized : Stmt.stmt_ext -> bool
  val contract_ext_is_recognized : Stmt.contract_ext -> bool
```

These functions are used in Raven's AST to be able to print the new constructs, or collect certain information about statements, such as local variables and fields accessed.

In each of these functions, the programmer is expected to case match on the corresponding extension argument (type_ext/expr_ext/stmt_ext/contract_ext), and match for all the cases that are declared in this extension. For any unknown case, the extension is required to defer to the remaining extensions by calling the same functionality from the `Cont` module.

If a construct category is not modified in the extension, its functions need no definition at all: `include Cont` at the top of the module (see [Overview](#overview)) already covers `type_ext_to_name`/`expr_ext_to_string`/etc. with `Cont`'s own behavior. You'll still see the explicit form, `let type_ext_to_name = Cont.type_ext_to_name`, here and there in the existing extensions and in this document's examples -- it's equivalent, just spelled out for the sake of the walkthrough.

There are two parallel families here for statements, one per `stmt_ext` extension point (see [Overview](#overview)): `pr_basic_stmt_ext`/`basic_stmt_ext_symbols`/`basic_stmt_ext_local_vars_modified`/`basic_stmt_ext_fields_accessed` for the flat, `basic_stmt_desc`-level `BasicStmtExt`, and `pr_stmt_ext`/`stmt_ext_symbols`/`stmt_ext_local_vars_modified`/`stmt_ext_fields_accessed` for the self-contained, `stmt_desc`-level `StmtExt` (see [Statement-bodied extensions](#statement-bodied-extensions-stmtext-at-the-stmt_desc-level) below). The only difference in shape between the two families is that the `basic_stmt_ext_*` versions take an extra `expr list` argument (the flat argument list `BasicStmtExt` carries alongside the tag) that the `stmt_ext_*` versions don't need, since a `StmtExt` value already owns its whole payload.

The `pr_basic_stmt_ext`/`pr_stmt_ext` commands take a `stmt_ext` (and, for the `basic_stmt_ext` family, an `expr_list`, a list of expressions). The programmer is supposed to fill in how to print this statement. Certain assumptions can be made about the number and types of arguments; these are usually guaranteed by type-checking or the parser. The programmer can thus throw internal errors if this is violated, as seen in [sampleExt.ml](../../lib/ext/sampleExt/sampleExt.ml).

`contract_ext_to_string` is this family's counterpart for contract clauses, but simpler in shape: since a `contract_ext` value owns its whole payload already (there's no separate `expr_list` argument), it's just a plain string-returning function, the same shape as `expr_ext_to_string`. [decreasesExt.ml](../../lib/ext/decreasesExt/decreasesExt.ml) renders its `Decreases specs` as `"decreases e1, e2, ..."` by printing each spec's `spec_form`.

`basic_stmt_ext_symbols`/`stmt_ext_symbols` are functions that are almost always expected to return `Set.empty (module QualIdent)`, but included for future expansion. There is no `contract_ext_symbols` counterpart: `Callable.symbols` (used for dependency analysis) treats a `stmt_ext`'s contribution as always empty too, so `contract_ext` simply isn't consulted there either -- a pre-existing limitation, not something specific to contracts. `AssertWithExt` (see [Statement-bodied extensions](#statement-bodied-extensions-stmtext-at-the-stmt_desc-level)) deliberately keeps this same "always empty" default for its own `StmtExt` value rather than recursing into the nested proof block it carries, for a reason worth knowing if you're tempted to do better: its `StmtExt` is always lowered away long before any pass that would consult `stmt_ext_symbols` runs, and the block still contains raw `VarDef` nodes at this point, which `Stmt.stmt_local_vars_modified` (the counterpart these three feed) rejects once lowering has normally already turned them into `Havoc`s elsewhere in the pipeline.

`basic_stmt_ext_local_vars_modified`/`basic_stmt_ext_fields_accessed` and their `stmt_ext_*` counterparts are the functions with which the programmer lets Raven know what variables to refresh and what fields to model when encoding the program into logical constraints. These functions have a return type of `ident list` and `qual_ident list` respectively, and are expected to return which local variables and fields are updated by a specific command. In [sampleExt.ml](../../lib/ext/sampleExt/sampleExt.ml) we see the use of `Expr.to_qual_ident`, `QualIdent.is_local` and `QualIdent.to_ident` functions. These are all implemented in `lib/ast/astDef.ml`, and discussed more thoroughly in [Userful Functions](#useful-functions). 

In `basic_stmt_ext_local_vars_modified`, we return the `lhs_expr` converted to an ident if it is "local", ie, does not refer to a global variable, and importantly does not have module qualifiers in its `qual_ident`. Otherwise we return `[]`. In `basic_stmt_ext_fields_accessed` we return `[]` always.

`stmt_ext_atomicity` answers how much of the *one* atomic step Raven allows while an invariant is unfolded or an atomic update is in flight your statement consumes: `NoStep` (ghost -- nothing an interfering thread can observe), `AtomicStep` (exactly one), or `NonAtomicStep` (not permitted there at all). Unlike everything else in this section, it is a question the atomicity analysis (`lib/frontend/rewrites/atomicityAnalysis.ml`) cannot answer for itself by looking at what your statement becomes: that pass has to run *before* `rewrite_basic_stmt_ext`/`rewrite_stmt_ext` lower it, because the lowering is generally several statements even when the source construct is one indivisible step. `AtomicExt`'s `cas` is the standard example -- it lowers to a field read plus a conditional field write, which counted separately would be two steps and would make `cas` unusable inside an open invariant, the one place it is actually needed. One function covers both extension points, since the analysis meets a `BasicStmtExt` and a `StmtExt` alike as an opaque tag; `StmtExt`'s nested statements are *not* walked (`Rewriter.Stmt.descend` doesn't enter them), so fold whatever they do into your own answer. The base of the chain answers `NonAtomicStep`, the conservative choice: an unclassified statement gets rejected inside an atomic block rather than waved through as free. Outside one the answer is never consulted, so a construct that could not appear in an atomic block anyway need not implement this at all.

`type_ext_is_recognized`/`expr_ext_is_recognized`/`stmt_ext_is_recognized`/`contract_ext_is_recognized` answer a narrower question than every other function in this section: not "what does this construct mean" but just "did *this extension itself* (not `Cont`) declare this specific constructor" -- implemented the same chain-deferral way (match your own constructors as `true`, defer everything else to `Cont`), so calling one on the currently-active chain answers "does *any* extension in this chain recognize it", same as the others. Note that `stmt_ext_is_recognized` is *shared* between the two `stmt_ext` extension points -- there's no separate `basic_stmt_ext_is_recognized` -- since it only answers "is this specific constructor mine", regardless of which of the two shapes (`BasicStmtExt`'s flat payload or `StmtExt`'s self-contained one) that constructor is meant to be embedded under. The only consumer is [`lib/ext/ext.ml`](../../lib/ext/ext.ml): when the active chain's `type_check_*` hits its terminal `DefaultExt` case (meaning nothing in the active chain recognized the construct), it uses these -- called against every *other* known `--extension` chain -- to check whether some other chain would have, and if so names that flag in the error (`this expression belongs to the 'eris' extension; re-run with --extension eris`) instead of a bare "no active extension recognizes this". If your extension declares no constructors of a given kind, defer the whole function to `Cont` directly, same as `type_ext_to_name`/`expr_ext_to_string` above:
```ocaml
  let type_ext_is_recognized = Cont.type_ext_is_recognized
```

These functions end up as fields of `Ast.Rewriter.ext_hooks` (see [Wiring](#wiring-how-ext_hooks-reaches-your-code) above) -- `type_ext_to_name`/`expr_ext_to_string`/`pr_basic_stmt_ext`/`pr_stmt_ext`/`contract_ext_to_string` back the *default* AST printers (`AstDef.Type.pr`, `AstDef.Stmt.pr`, `AstDef.Callable.pr`, etc., built via each module's `make_printers`) whenever they hit a `TypeExt`/`ExprExt`/`BasicStmtExt`/`StmtExt` leaf or a `call_decl_contract_ext`/`loop_contract_ext` entry, and `basic_stmt_ext_symbols`/`stmt_ext_symbols`/etc. are read the same way by `AstDef.Stmt`'s `symbols`/`stmt_local_vars_modified`/`stmt_fields_accessed`. You don't call any of this machinery yourself; it's what makes printing and dependency analysis work correctly on ASTs that still contain your extension's constructs. The `_is_recognized` functions are the one exception: they aren't installed into `ext_hooks` directly (there'd be nothing to install -- see [`suggest_extension_for_type_ext`](../../lib/ext/ext.ml) & co., which *are* installed, and are computed once in `lib/ext/ext.ml` by calling these across every known chain); you still implement them the same chain-deferral way as everything else here.

#### Printing and logging from your extension

If your own `type_check_*`/`rewrite_*_ext` implementation needs to print or log an expression, statement, or type -- for debugging, or as part of an error message -- reach for `Rewriter.current_printers` rather than `AstDef.Type.pr`/`AstDef.Expr.pr`/`AstDef.Stmt.pr` directly. The bare `AstDef` printers only know about the *default* stub rendering of `*_ext` leaves; `Rewriter.current_printers` reads the `printers` record built from whichever extension is actually active out of the `Rewriter.t` state, so it renders correctly even when the fragment you're printing embeds another extension's constructs (relevant once extensions are stacked, as `DecreasesExt`/`AssertWithExt`/`MatchExt`/`ProphecyExt`/`ErrorCreditsExt` are in `lib/ext/ext.ml`):

```ocaml
let* printers = Rewriter.current_printers in
Logs.debug (fun m -> m "my_ext: got expr %a" printers.pr_expr expr)
```

For debug logging specifically, `Rewriter.Logs.debug`/`info`/`warn`/`err`/`app` fold the `current_printers` lookup into the log call itself, so the common case is one line instead of two -- and the lookup is skipped entirely when that log level isn't enabled, same as plain `Logs.debug`:

```ocaml
let* () = Rewriter.Logs.debug (fun printers m ->
    m "my_ext: got expr %a" printers.pr_expr expr) in
```

Both of these require being inside the `Rewriter.t` monad (i.e. `let open Rewriter.Syntax in ... let*`/`let+`), which every `type_check_*`/`rewrite_*_ext` function already is. See [errorCreditsExt.ml](../../lib/ext/errorCreditsExt/errorCreditsExt.ml), [prophecyExt.ml](../../lib/ext/prophecyExt/prophecyExt.ml), [AtomicExt.ml](../../lib/ext/atomicExt/AtomicExt.ml), or [listExt.ml](../../lib/ext/listExt/listExt.ml) for real examples of both styles.

### Rewriter

This API contains the following functions which are used by Raven to perform any _type_ (or, for contracts, _expression_) rewrites on the extensions if necessary:

```ocaml
  val expr_ext_rewrite_types :
    f:(type_expr -> type_expr Rewriter.t)
    -> Expr.expr_ext 
    -> Expr.expr_ext Rewriter.t

  val basic_stmt_ext_rewrite_types :
    f: (type_expr -> type_expr Rewriter.t) 
    -> Stmt.stmt_ext 
    -> Stmt.stmt_ext Rewriter.t

  val stmt_ext_rewrite :
    f:(expr -> expr Rewriter.t)
    -> c:(Stmt.t -> Stmt.t Rewriter.t)
    -> Stmt.stmt_ext
    -> Stmt.stmt_ext Rewriter.t

  val contract_ext_rewrite_exprs :
    f:(expr -> expr Rewriter.t)
    -> Stmt.contract_ext
    -> Stmt.contract_ext Rewriter.t
```

`expr_ext_rewrite_types`/`basic_stmt_ext_rewrite_types` are only required if the expression or (flat, `basic_stmt_desc`-level) statement extensions defined in this extension store types. Please take a look at [prophecyExt](../../lib/ext/prophecyExt/prophecyExt.ml) to see a non-trivial example implementation of these functions.

`stmt_ext_rewrite` is `basic_stmt_ext_rewrite_types`'s counterpart for the self-contained, `stmt_desc`-level `StmtExt` (see [Statement-bodied extensions](#statement-bodied-extensions-stmtext-at-the-stmt_desc-level) below), but broader: since a `StmtExt` value can carry both expressions *and* a nested `Stmt.t`, it takes two callbacks -- `f` to apply to every expression your value carries (the same role `expr_ext_rewrite_types`/`basic_stmt_ext_rewrite_types` play, just not restricted to type substitution: `f` is instantiated with plain expression substitution, type substitution, or qualified-identifier substitution depending on which generic traversal reached your node), and `c` to apply to every nested `Stmt.t` your value carries, so it can recurse into its own embedded statements the same way core `Cond`/`Loop` nodes do. [assertWithExt.ml](../../lib/ext/assertWithExt/assertWithExt.ml) implements it by applying `f` to its `spec.spec_form` and `c` to its `proof` block.

`contract_ext_rewrite_exprs` plays the analogous role for `contract_ext`, except it rewrites *expressions*, not types (a `contract_ext` value doesn't have a separate type-carrying slot the way `NewProph (bool, type_expr)` does for `stmt_ext` -- what it carries are the expressions of the clause itself, e.g. each measure's `spec_form` for `decreases`). Applying `f` to every expression your value carries is what lets generic code -- currently, substitution during higher-order module instantiation -- rewrite a contract clause without knowing what it means. [decreasesExt.ml](../../lib/ext/decreasesExt/decreasesExt.ml) implements it by mapping `f` over each `spec.spec_form` and rebuilding the `Decreases` value.

In [sampleExt.ml](../../lib/ext/sampleExt/sampleExt.ml), we simply skip these functions, setting them equal to the one from `Cont`.

Like the AstDef functions above, these end up as `ext_hooks` fields, read out of the `Rewriter.t` state deep inside `Rewriter.Expr.rewrite_types`/`Rewriter.Stmt.rewrite_types`/`Rewriter.Stmt.rewrite_expressions`/`Rewriter.Stmt.rewrite_qual_idents` (the generic substitution traversals used e.g. when instantiating higher-order modules) whenever one reaches an `ExprExt`/`BasicStmtExt`/`StmtExt` node, or (for `contract_ext_rewrite_exprs`) inside the analogous generic expression-substitution traversal over a loop's `loop_contract_ext` -- not something your own code calls directly. One exception worth knowing about: `Rewriter.Stmt.descend`, the generic structural recursor used pervasively by rewrite passes throughout `lib/frontend/rewrites/` (via `f:c` callbacks with a *custom* accumulator state, e.g. atomicity analysis, skolemization), does *not* descend into a `StmtExt` node, even though it does descend into `Block`/`Loop`/`Cond` -- every `ext_hooks` field (including `stmt_ext_rewrite`) is fixed at the plain, no-extra-state `Rewriter.t`, and calling it from inside `descend` would force *every* caller of `descend` onto that same fixed state, breaking the richer-state callers. In practice this only matters if a pass built on `descend` needs to reach into an *unlowered* `StmtExt`'s nested statements; since a `StmtExt` is expected to already be rewritten away (via `rewrite_stmt_ext`, [Statement-bodied extensions](#statement-bodied-extensions-stmtext-at-the-stmt_desc-level) below) long before such a pass runs, this is a corner rather than a routine concern.

### Typing

This API contains the following functions which are used by Raven to type-check any newly defined types, expressions and statements:

```ocaml
  val type_check_type_expr : Type.type_ext -> type_expr list -> Type.type_attr -> type_check_type_expr_functs -> type_expr Rewriter.t

  val type_check_expr : Expr.expr_ext -> expr list -> Expr.expr_attr -> type_expr -> type_check_expr_functs -> expr Rewriter.t

  val type_check_basic_stmt : 
    Callable.call_decl ->
    Stmt.stmt_ext -> expr list ->
    location ->
    ProgUtils.DisambiguationTbl.t ->
    type_check_stmt_functs ->
    (Stmt.basic_stmt_desc * ProgUtils.DisambiguationTbl.t) Rewriter.t

  val type_check_stmt_ext :
    Callable.call_decl ->
    Stmt.stmt_ext ->
    location ->
    ProgUtils.DisambiguationTbl.t ->
    type_check_stmt_functs ->
    (Stmt.stmt_desc * ProgUtils.DisambiguationTbl.t) Rewriter.t
```

These type signatures are a bit more complicated. Let's go through them one at a time.

For `type_check_type_expr`:
- It takes the `type_ext` and the `type_expr list` as arguments. These constitute the definition of the new type. 

- The `type_attr`, defined in [astDef.ml](../../lib/ast/astDef.ml) refers to _type attribute_, which contains a _location_ as well as ghost status. This location is tied to input location which is used to show to the user the relevant pieces of code for a given error. 

- The next argument is of type `type_check_type_expr_functs`, which is a record object storing a set of functions that are useful during type-checking `type_expr`s. At present, this only contains the `process_type_expr` function which is originally defined in [typing.ml](../../lib/frontend/typing.ml). This function is used to process any sub-expressions during the processing of the current type_expr. This type (along with `type_check_expr_functs` and `type_check_stmt_functs` below) is actually defined in [rewriter.ml](../../lib/ast/rewriter.ml), not `extApi.ml` -- it has to live there so that `Ast.Rewriter.ext_hooks` can mention it without `lib/ast` depending on `lib/ext`. [extApi.ml](../../lib/ext/api/extApi.ml) re-exports it under the same name via `type type_check_type_expr_functs = Rewriter.type_check_type_expr_functs = { ... }`, so this distinction shouldn't matter in practice; you can keep referring to it by its `ExtApi`-qualified name.

- Finally, it has a return type of `type_expr Rewriter.t`. `Rewriter.t`, defined in [rewriter.ml](../../lib/ast/rewriter.ml), is a monad that carries Raven's symbol table state throughout the program, letting us do things like seamlessly look up symbol definitions from the program. We use the `let*` and `let+` bindings from `Rewriter.Syntax` in order to interact with this monad. We also use the `Rewriter.return` to wrap a normal value into the monad. In general, keeping the monad in mind is very useful, specially with higher-order functions. The Rewriter module contains its own implementations for commonly used functions such as `List.map`, and `List.fold_right`, implemented in [state.ml](../../lib/util/state.ml).

Here, `type_expr Rewriter.t` refers to the fact that this function returns a `type_expr`, wrapped inside the `Rewriter` monad.

Similarly, for `type_check_expr`:
- It takes the `expr_ext` and `expr list` as arguments, which constitute the new expression.

- The `expr_attr` defined in [astDef.ml](../../lib/ast/astDef.ml) refers to _expression attributes_, which contain a location as well as the expression's _type_.

- The next argument of type `type_expr` is the _expected type_ of the expression being type-checked. This is often `Type.Any`, but can include typing hints from the environment.

- The next argument, of type `type_check_expr_functs`. This is the set of functions from [typing.ml](../../lib/frontend/typing.ml) that are useful while type-checking expressions. Please refer to [Useful Functions](#useful-functions) to identify how to use each of these functions.

As for `type_check_basic_stmt`, the goal of this function is to make sure the statement is well-formed with well-typed arguments. It has a considerably more complex type signature. In particular, it has a `call_decl` that contains information about the parent callable of this `stmt_ext`. It also contains a `ProgUtils.DisambiguationTbl.t`, which is a local, per-callable data-structure used to disambiguate local variables, for instance using the same variable in multiple different scopes. This procedure also returns a _disambiguation table_ which contains any updates made during type-checking the present statement. As usual, `type_check_stmt_functs` contains a list of useful functions. Notably, `disambiguate_process_expr` and `disam_tbl_add_var_decl` makes use of, and updates the disambiguation table respectively.

In [sampleExt.ml](../../lib/ext/sampleExt/sampleExt.ml), we first case-match on `RandEven`. For a sample statement like
  `x := randEven(n);`,
this gets parsed with `lhs_expr` denoting `x` and `n_expr` denoting `n`.

We use a function from `type_check_stmt_functs` to get the variable declaration for the `lhs_expr`. Once we get its `var_type`, we check to make sure it is an `Int` type, otherwise we throw a `type_mismatch_error`. Then we typecheck `n_expr` using `Type.int` or `Int` as the expected type. At this point we are ready to return the updated statement, constructed with the `Stmt.BasicStmtExt` constructor denoting an extension statement, along with `disam_tbl`. 

If the arguments are not what we expect, then we throw a type error straightaway. And if it is an unknown constructor, then we defer to the continuation extension `Cont`, as usual.

`type_check_stmt_ext` is `type_check_basic_stmt`'s counterpart for the self-contained, `stmt_desc`-level `StmtExt` (see [Statement-bodied extensions](#statement-bodied-extensions-stmtext-at-the-stmt_desc-level) below): it takes no separate `expr list`, since a `StmtExt` value owns its whole payload, and it returns a whole `Stmt.stmt_desc` rather than a `Stmt.basic_stmt_desc` -- it isn't constrained to stay "basic", and in fact [assertWithExt.ml](../../lib/ext/assertWithExt/assertWithExt.ml) uses that freedom to return the *fully lowered* result directly (a `Block`/`Cond` structure) rather than another `StmtExt` left for `rewrite_stmt_ext` to lower later, since it needs the whole synthesized structure type-checked as one unit -- see its own doc comment for why. `type_check_stmt_functs` gains one field beyond what `type_check_basic_stmt` gets: `process_stmt : Callable.call_decl -> Stmt.t -> ProgUtils.DisambiguationTbl.t -> (Stmt.t * ProgUtils.DisambiguationTbl.t) Rewriter.t`, letting you recursively type-check a whole nested `Stmt.t` (e.g. a proof block) the same way `Typing.process_stmt` type-checks an ordinary callable-body statement -- something `type_check_basic_stmt` never needs, since a `basic_stmt_desc` can't embed a nested statement in the first place.

`type_check_contract_ext` is `contract_ext`'s counterpart to `type_check_basic_stmt`/`type_check_stmt_ext`:

```ocaml
  val type_check_contract_ext :
    Callable.call_decl ->
    Stmt.contract_ext ->
    location ->
    ProgUtils.DisambiguationTbl.t ->
    type_check_stmt_functs ->
    Stmt.contract_ext Rewriter.t
```

It's called once per entry of a `call_decl_contract_ext`/`loop_contract_ext` list, and takes (and returns) a whole `Stmt.contract_ext` value -- unlike `type_check_basic_stmt`, there's no separate `expr list` alongside it, since a `contract_ext` constructor already carries whatever payload it needs, the same as `type_check_stmt_ext`. `call_decl` is the declaring callable (for a loop's clause, this is the `call_decl` of the tail-recursive procedure the loop is about to be desugared into -- loop contracts are type-checked before that desugaring runs, but the formal-scope shape is the same one the clause will end up with). `type_check_stmt_functs` is the same callback bundle `type_check_basic_stmt`/`type_check_stmt_ext` get -- including `process_stmt`, though a contract clause has no statement of its own to recurse into, so you're unlikely to need it here; `disambiguate_process_expr` is what you'll use to type-check the expressions your value carries.

[decreasesExt.ml](../../lib/ext/decreasesExt/decreasesExt.ml) case-matches on `Decreases specs`, and for each `spec` in the list, type-checks `spec.spec_form` against `Type.any` via `disambiguate_process_expr` (inferring its type rather than fixing it), then resolves that type's `WellFoundedOrder` instance (`is_wf_order_type`) and rejects the clause if it has none -- except for a self-recursive `data` type, where `is_wf_order_type` falls through to `as_data_type`/`auto_order_module_qual_ident` instead of failing, synthesizing a trusted `lt`-only module on the spot (see the extension overview above) and using its qual_ident as if it were a real instance's -- and installs a default error message into `spec.spec_error` (via `Stmt.mk_const_spec_error`) if one isn't already set -- this last part matters because of a wrinkle worth calling out for any extension whose clause can end up on a `rewrite_loops`-synthesized procedure: that procedure gets *re*-type-checked when it's introduced (`Rewriter.introduce_typecheck_symbol'`), so `type_check_contract_ext` will see the same clause a second time, by then already carrying whatever `rewrite_contract_ext_loop_transfer` (see [Contracts](#contracts) below) set on it -- overwriting `spec_error` unconditionally at that point would silently discard it.


#### Constructs that bind variables (`disambiguate_expr_ext`)

Everything above runs during type-checking. But a callable's body goes through one pass *before* any of it: `Typing.ProcessCallable`'s disambiguation pass, which alpha-renames every local variable to a fresh name (so that same-named variables in different scopes stay distinct) and rejects any identifier that isn't bound at that point. That pass walks the AST generically, which is fine for an extension construct whose sub-expressions are just ordinary expressions -- but *not* if your construct binds variables of its own that its sub-expressions refer to. Those references have no binder as far as the generic walk is concerned, so the body is rejected as unbound long before `type_check_expr` gets a chance to introduce them.

`disambiguate_expr_ext` is the hook for that case:

```ocaml
  val disambiguate_expr_ext :
    Expr.expr_ext ->
    expr list ->
    Expr.expr_attr ->
    ProgUtils.DisambiguationTbl.t ->
    disambiguate_expr_functs ->
    (Expr.expr_ext * expr list) Rewriter.t
```

It is called for every `Expr.ExprExt` node the pass meets, and returns the rewritten tag together with its rewritten sub-expressions. `disambiguate_expr_functs` carries a single callback, `disambiguate_expr : expr -> ProgUtils.DisambiguationTbl.t -> expr Rewriter.t`, which recurses into a sub-expression under whichever table you hand it -- choosing that table per sub-expression is the entire point of the hook. Build the extended table with `ProgUtils.DisambiguationTbl.push` (opens a scope) and `ProgUtils.DisambiguationTbl.add` (maps a source name to a fresh `Ident.fresh` one), the same way `Typing`'s own `Binder` case does for a quantifier's bound variables.

Two things to get right. First, return the *renamed* binders inside your tag: the sub-expressions now refer to the fresh names, so the names your `type_check_expr` later reads out of the tag must be those, not the ones the parser produced. Second, only the sub-expressions actually in scope of a binder should see the extended table -- a `match`'s scrutinee, for instance, is outside every arm.

Unlike the other hooks, the base of the chain implements this one for real rather than raising: `DefaultExt`'s version recurses into every sub-expression under the unchanged table and leaves the tag alone. That is exactly right for a construct that binds nothing, which is nearly all of them -- so **only implement this hook if your construct binds variables**. [matchExt.ml](../../lib/ext/matchExt/matchExt.ml) is the reference implementation: each `match` arm pushes a scope, renames the arm's pattern variables into it (leaving `_` out, so it binds nothing and may repeat), and disambiguates that arm's body under it.

### Rewrites

This section contains functions that perform essential rewrites to reduce the newly extended front-end features into built-in Raven constructs.


```ocaml
  val rewrite_type_ext : Ast.Type.type_ext -> type_expr list -> location -> type_expr Rewriter.t

  val rewrite_expr_ext : Expr.expr_ext -> expr list -> Expr.expr_attr -> expr Rewriter.t
  
  val rewrite_basic_stmt_ext : Stmt.stmt_ext -> expr list -> location -> Stmt.t Rewriter.t

  val rewrite_stmt_ext : Stmt.stmt_ext -> location -> Stmt.t Rewriter.t
```

These functions are more straight-forward to follow. Essentially for each new construct, we return an equivalent encoding of the data structure in "native" Raven. For instance, expressions can be translated into different expressions involving functions and heap expressions. Statements can be rewritten into equivalent set of statements, combined into one `Stmt.Block` stmt, often involving `inhale` and `exhale` statements, or field reads/writes, etc.

`rewrite_stmt_ext` is `rewrite_basic_stmt_ext`'s counterpart for the self-contained, `stmt_desc`-level `StmtExt` (see [Statement-bodied extensions](#statement-bodied-extensions-stmtext-at-the-stmt_desc-level) below); it drops the separate `expr list` for the same reason every other `StmtExt`-side function in this document does. Both are called from `Rewrites.rewrites_stmt_ext` (`lib/frontend/rewrites/rewrites.ml`), which walks the whole module once type-checking is complete and lowers every remaining `BasicStmtExt`/`StmtExt` node it finds -- as noted under [Rewriter](#rewriter) above, if your `type_check_stmt_ext` already returns the fully lowered result (as `AssertWithExt`'s does), your `rewrite_stmt_ext` implementation for that constructor is unreachable in practice; treat that as an invariant to assert, not skip silently, the way [assertWithExt.ml](../../lib/ext/assertWithExt/assertWithExt.ml) does.

In [sampleExt.ml](../../lib/ext/sampleExt/sampleExt.ml), we introduce one `havoc` statement, to havoc the value of the lhs expression, and then inhale a statement expressing constraints about the newly-assigned value.

There is no `rewrite_contract_ext` counterpart to the three functions above: a contract clause isn't one node to rewrite into an equivalent "native" encoding, it's a property that has to be enforced by instrumenting the *body* of whichever callable it's attached to (e.g. inserting a check before every recursive call). That's what [Contracts](#contracts), below, is for. One more function belongs here, though, since it isn't specific to contracts at all:

```ocaml
  val rewrite_callable_entry :
    Callable.call_decl -> Stmt.t list Rewriter.t
```

`rewrite_callable_entry` is called once for every `Proc`/`Lemma` callable, before any of its statements are visited by anything else, and returns statements to prepend at the very top of the callable's body -- unconditionally, for every such callable in the program, regardless of whether your extension has anything to do with it; the default (no extension using this hook) is to prepend nothing, so implementing it is opt-in per extension the same way every other hook here is. This is the general-purpose tool for a need that doesn't have a dedicated config value: introducing (via `Rewriter.introduce_symbol`) and initializing your own local variables, sized/typed/named however a *specific* callable requires, rather than a fixed set added uniformly (and mostly unused) to every callable. [decreasesExt.ml](../../lib/ext/decreasesExt/decreasesExt.ml) uses this to snapshot a `decreases` measure's entry-time value into a ghost local variable -- necessary because the callable's own formals may be reassigned later in the body (e.g. a loop counter), so "the measure at entry" can't just mean "the clause's expressions evaluated at the formals" read back at the call site. It declares that variable here with a *tuple* type built from each component's own type (a measure component can be any type with a `WellFoundedOrder` instance, not just `Int`) and sized to exactly as many components as this specific callable's `decreases` clause has (via `Type.mk_prod`; `Type.mk_prod`/`Expr.mk_tuple`/`Expr.mk_tuple_lookup` all collapse the single-component case to a bare value of that one component's type, so `decreases n` doesn't pay for tuple-ness it doesn't need), checking first (via a small helper that looks for a `decreases` clause on the given `call_decl`) whether there's anything to do at all -- most callables have no `decreases` clause, so this is a no-op for those.


### Statement-bodied extensions (`StmtExt` at the `stmt_desc` level)

Everything under [AstDef](#astdef)/[Rewriter](#rewriter)/[Typing](#typing)/[Rewrites](#rewrites) above comes in two parallel families for statements, because `Stmt.basic_stmt_desc` (the running `RandEven` example throughout this document) has no case that can embed a nested `Stmt.t`:

```ocaml
type basic_stmt_desc =
  | VarDef of var_def
  | Spec of spec_kind * spec
  (* ... every other "leaf" statement kind: Assign, FieldRead, Havoc, Use, Fpu, ... *)
  | BasicStmtExt of (stmt_ext * expr list)

and stmt_desc =
  | Block of block_desc
  | Basic of basic_stmt_desc
  | Loop of loop_desc
  | Cond of cond_desc
  | StmtExt of stmt_ext
```

If your construct is just an argument list -- like `RandEven`, or `AtomicExt`'s `cas`/`faa`/`xchg`/`cmpxchg` -- declare it as a `BasicStmtExt` and use the `..._basic_stmt_ext_...`/`type_check_basic_stmt`/`rewrite_basic_stmt_ext` family documented above; this is the common case, and everything above this section describes it. But if your construct needs to carry a *nested statement* -- a block of Raven code that's semantically part of the construct itself, not just its arguments -- declare it as a `StmtExt` instead, a sibling of `Block`/`Loop`/`Cond` rather than one more case nested inside `Basic`, and use the `..._stmt_ext_...`/`type_check_stmt_ext`/`rewrite_stmt_ext` family instead. Both extension points share the same underlying `type Stmt.stmt_ext = ..`; which family a given constructor uses is determined entirely by which case (`BasicStmtExt`'s tuple, or `StmtExt` directly) you wrap it in when you construct or match on it, not by anything in the constructor's own declaration.

`AssertWithExt` (`lib/ext/assertWithExt/`, see [AssertWith Extension](#assertwith-extension) above) is the reference implementation: `assert e with { proof }` needs `proof` -- an arbitrary block of ghost Raven code, checked and then discarded -- to be part of the statement itself, so it declares

```ocaml
type Stmt.stmt_ext +=
  | AssertWith of { spec : Stmt.spec; proof : Stmt.t }
```

and constructs `Stmt.StmtExt (AssertWith { spec; proof })` directly (no `expr list`, no `Basic` wrapper), from `lib/ext/assertWithExt/assertWithExt_parser.mly`'s grammar action.

A few consequences worth knowing before you reach for this shape:

- **Parsing.** The grammar rule producing your construct returns a `Stmt.stmt_desc list` the same way every other `stmt`-level alternative does (see [Creating a New Extension](#creating-a-new-extension)); just build `Stmt.StmtExt (YourConstructor { ... })` instead of `Stmt.Basic (BasicStmtExt (YourConstructor, args))`. If your construct needs a nested block, add `%public block` (already exported by core `parser.mly`) to your grammar rule to parse it: `assertWithExt_parser.mly`'s production is `sk = SPEC; e = expr; WITH; b = block; { ... }`.
- **Type-checking can fully resolve the construct, not just check it.** `type_check_stmt_ext` returns a whole `Stmt.stmt_desc`, not constrained to be another `StmtExt` -- if your rewrite needs the *entire* synthesized structure (including any locals it introduces) type-checked as one unit, rather than checked once now and lowered separately later, you can build the raw, not-yet-type-checked target structure and run all of it through the new `process_stmt` field of `type_check_stmt_functs`, then return the result directly. This is exactly what `AssertWithExt` does, and its own doc comment on `type_check_stmt_ext` explains why: a synthesized `VarDef` (e.g. its fresh `$nondet` nondeterminism variable) needs to go through the same VarDef-to-`Havoc` conversion and symbol registration ordinary statements get from `Typing.process_stmt`, which doesn't happen for free if you build it later, in `rewrite_stmt_ext`, after type-checking has already finished. If your construct doesn't have this wrinkle, the simpler, more common shape -- check the pieces, return another `StmtExt` carrying the checked payload, and do the actual lowering in `rewrite_stmt_ext` -- works fine too, and is a closer match to how `BasicStmtExt` extensions are usually written.
- **`Rewriter.Stmt.descend` doesn't recurse into an unlowered `StmtExt`.** See the note at the end of [Rewriter](#rewriter) above -- in practice this means your `StmtExt` should be lowered (by `rewrite_stmt_ext`, or resolved away entirely by `type_check_stmt_ext` as above) before any pass that relies on `descend` to reach statements nested inside it runs. Since `Rewrites.rewrites_stmt_ext` runs right after type-checking, ahead of the bulk of `lib/frontend/rewrites/`'s passes, this is the default outcome, not something you need to arrange yourself -- it only becomes a real constraint if you're deliberately deferring lowering later than that.
- **`symbols`/`local_vars_modified`/`fields_accessed` default to empty, safely.** As noted under [AstDef](#astdef) above, `AssertWithExt` keeps the default "always empty" answer for `stmt_ext_symbols`/`stmt_ext_local_vars_modified`/`stmt_ext_fields_accessed` rather than recursing into its nested `proof`, precisely because that block can still contain raw `VarDef`s at the point these might run, which the corresponding `Stmt.stmt_local_vars_modified` et al. reject outside of extension code too. If your own construct is lowered promptly and its nested statement never contains an un-lowered `VarDef` when these could plausibly be called, recursing into it (via the ordinary `Stmt.symbols`/`Stmt.stmt_local_vars_modified`/`Stmt.stmt_fields_accessed` functions, applied to your own nested `Stmt.t` field) is a reasonable improvement over the default -- just be sure of the ordering before you do.


### Contracts

A `contract_ext` extension's job is different in kind from the other three: `type_ext`/`expr_ext`/`stmt_ext` are each a single AST node that gets type-checked and then rewritten away into simpler terms, in isolation. A contract clause instead describes a property of an entire callable (or loop), so an extension needs to (a) type-check the clause once, against the declaring callable's formals, and (b) find every place in that callable's body -- specifically, every recursive call -- where the property needs to be instrumented. Declaring the extension point itself works the same way as the other three:

```ocaml
type Stmt.contract_ext +=
  | Decreases of Stmt.spec list
```

Unlike `stmt_ext`/`expr_ext`/`type_ext`, there's no separate `expr list` carried alongside the tag in an AST node -- `call_decl_contract_ext`/`loop_contract_ext` are plain `Stmt.contract_ext list` fields on `Callable.call_decl`/`Stmt.loop_desc`, and each list entry is one self-contained `contract_ext` value. So your constructor should carry whatever payload it needs directly. [decreasesExt.ml](../../lib/ext/decreasesExt/decreasesExt.ml)'s `Decreases of Stmt.spec list` is one `Stmt.spec` per measure component (`decreases n, m` desugars to two specs) precisely so it can reuse `spec`'s existing `spec_form`/`spec_comment`/`spec_error` fields, the same way `call_decl_precond`/`loop_contract` already do -- this is what lets a `decreases` clause participate in Raven's normal located, worded error-reporting machinery instead of needing its own.

The type-checking and printing/rewrite-type hooks for `contract_ext` (`type_check_contract_ext`, `contract_ext_to_string`, `contract_ext_rewrite_exprs`) are documented in [AstDef](#astdef), [Rewriter](#rewriter), and [Typing](#typing) above alongside their `stmt_ext`/`expr_ext`/`type_ext` counterparts. `rewrite_callable_entry`, documented under [Rewrites](#rewrites) just above, is also commonly relevant here (that's exactly how `DecreasesExt` uses it) but isn't `contract_ext`-specific itself. What's new here are two functions with no peer among the other three extension points, because they instrument calls between callables rather than rewriting one node:

```ocaml
  val rewrite_contract_ext_call :
    Callable.call_decl ->
    Callable.call_decl ->
    expr list ->
    location ->
    Stmt.t list Rewriter.t

  val rewrite_contract_ext_loop_transfer :
    subst:(expr -> expr) -> Stmt.contract_ext -> Stmt.contract_ext
```

`rewrite_contract_ext_call` is called once for every call site whose *callee* has a non-empty `call_decl_contract_ext`: for every `Stmt.Call` inside a `Proc`/`Lemma` body, and, for `Func`s (whose body is a pure expression, so there's no statement of their own to instrument), at every call `Rewrites.rewrite_add_func_contract_lemmas` emits into a callee's auto-generated contract-checking lemma. `caller_call_decl`/`callee_call_decl` are the calling and called callable's declarations, the `bool` says whether caller and callee lie in the same strongly-connected component of the module's call graph (`true` for a literal self-call, and also `true` for any two callables mutually recursive with each other, even through intermediate calls -- computed once per module from the whole call graph, see `lib/frontend/rewrites/rewrites.ml`), and `call_args` are the actual arguments of that call. The function returns statements (typically an `assert`) to insert immediately before it. Core code calls this uniformly for every such call site -- it doesn't know what `call_decl_contract_ext` means, only that some extension might want to instrument the call, and critically **this is not limited to recursive calls**: caller and callee can be any two (or the same) callable, and the `bool` is `false` for an unrelated pair; it's up to your implementation to decide, from `caller_call_decl`/`callee_call_decl`/the `bool`, whether and how they're related. [decreasesExt.ml](../../lib/ext/decreasesExt/decreasesExt.ml) only acts when the `bool` is `true`, i.e. for calls within a recursive group, self- or mutually-recursive alike (with a separate check, `check_contract_ext_group_compatible`, requiring every member of a >1-member group to declare a `decreases` clause of matching arity and `WellFoundedOrder` instance, or reject the whole group as a type error) -- but a different contract extension enforcing something that has to hold at *every* call to a given callable, recursive or not, needs no different hook or pass to do that: it would simply not filter on the `bool` at all. Do bear in mind that since core can no longer cheaply skip most calls (it has to resolve and look up every callee to check its `call_decl_contract_ext`, one symbol-table lookup per call site), this does cost a little more than a recursion-only version would; that cost only escalates further (an extra lookup of the caller too) once a callee's `call_decl_contract_ext` is actually non-empty, which is rare.

`rewrite_contract_ext_loop_transfer` is called by `Rewrites.rewrite_loops` for every entry of a loop's `loop_contract_ext`, as that function desugars the loop into a self-recursive tail-call procedure and transfers the loop's own contract onto it -- the same way it already transfers `loop_contract` onto the new procedure's `call_decl_precond`/`call_decl_postcond`. `subst` is that same substitution (loop-local variables -> the synthesized procedure's fresh formals); apply it to whatever expressions your value carries, and use the opportunity to swap in more accurate wording if your default message would otherwise refer to the callable currently being checked (which, for a loop, is an internal, synthesized name the user never wrote). [decreasesExt.ml](../../lib/ext/decreasesExt/decreasesExt.ml) does this by rebuilding each spec's `spec_error` to say "this loop may not terminate" instead of "this recursive call...", capturing `Expr.to_loc spec.spec_form` *before* calling `subst` -- substituting a bare-identifier expression (e.g. the common case `decreases i`) replaces the whole node, which would otherwise lose its source location. This is the same technique `Rewrites.rewrite_stmt_error_msg`'s `Loop` case already uses to word failing-invariant errors correctly, not just a similar one. Once this transfer is done, the synthesized procedure is just another self-recursive `Proc` as far as `rewrite_contract_ext_call` is concerned, so loop termination checking needs no separate code path at all.

Because these two functions (and `rewrite_callable_entry`) instrument callable bodies/calls rather than rewriting one node, none of them are things you call yourself, and (unlike `rewrite_stmt_ext`, say) there's no expectation that every contract-extending extension implements both meaningfully -- the defaults (no active contract extension) are all no-ops or the identity, so implementing only what your extension actually needs and deferring the rest to `Cont` is normal.


### Epilogue

This contains a value that properly propagates and accumulates the configuration from successive extensions. There is usually no need to modify it, which is why this section carries a warning in the comments.

```ocaml
  val lib_sources : (string * string) list
```

This is read directly off the `(module ExtApi.Ext)` value chosen by `--extension`, once in `bin/raven.ml`, before type-checking even starts, to assemble the standard library source (see `parse_and_check_all`).

This sums up the API itself. In the next section we will discuss many commonly used functions in the Raven code-base, and other relevant code in order to provide a starting point into the code-base. At present, the best way to understand how to use each of these functionalities is to read the code, find references to specific functions and see how they're being used. Please contact the authors if you're interested, we will be happy to give a walkthrough, discuss specific extension designs, and answer any questions you may have.

<!-- We will try our best to add documentation and comments to extensions and the code-base in general. -->


## Useful Functions

In order to correctly implement the right type-checking and rewrite strategies, certain Raven functionality is invaluable. In order to orient a new programmer with the different functionalities, where they are located, and best practices when creating an extension, we provide an overview of certain commonly-used functions and how the rest of the code is organized. Here is a list of notable functions from different sections:


### [Typing](../../lib/frontend/typing.ml)

This file contains the code for type-checking Raven AST. It is broadly divided into 4 sections:
- ProcessTypeExpr
- ProcessExpr
- ProcessCallable
- ProcessModule

Each of these contain functions for type-checking the corresponding constructs. Following is the list of functions that we pass explicitly to type-checking functions in extensions. We briefly describe what they do as well as their signatures.

- process_type_expr: Type-checks `type_expr`. Takes a `type_expr` argument and returns `type_expr Rewriter.t`, which is a `type_expr` wrapped in the `Rewriter` monad.

- check_and_set: It takes an expression, and three type expressions. These denote a _type lowerbound_, a _type upperbound_ and an _expected type_. Types in Raven form a lattice. This function checks that the expected type satisfies the upper and lower bounds, and then returns an expression with the type updated appropriately. Otherwise it throws a `type_mismatch` error. This function is used in `process_expr` to make sure the given expressions satisfy certain type constraints.

- process_expr: It takes an expression, an expected type, and returns an `expr Rewriter.t`, which is the type-checked expression. It can (and should!) raise `type_errors` when ill-typed input is passed.

- type_mismatch_error: It raises a `type_error`. It takes a `location`, an expected type, and a found type.

- get_assign_lhs: It takes a `qual_ident`, and returns a fully qualified `qual_ident`, as well as a variable declaration `var_decl` of the variable being referenced in the `qual_ident`. This function is used when type-checking statements that assign a value to an "lhs" argument, to look up the "lhs" expression.

- expand_type_expr: This takes a `type_expr`, and returns another `type_expr Rewriter.t`. It basically recursively expands all the types referencing other types. For instance, if we have `type T1 = Int; type T2 = T1;`, this function will expand type `T2` into `Int`.

- disambiguate_process_expr: While type-checking statements, Raven utilizes a local _disambiguation table_ for each callable, in order to have unique local variable names, and resolve same name being used in multiple different scopes, etc. This process is called _disambiguating_ expressions, ie renaming local variables according to the `disamTbl`. This function combines the _disambiguating_ and _processing_ of expressions. This function takes an expression, an expected type, as well as a disambiguation table. When type-checking statements, one should always use `disambiguate_process_expr` and not `process_expr`.

- disam_tbl_add_var_decl: This function handles a new variable declaration and updates the `disam_tbl` appropriately. It takes a `var_decl` and a `disam_tbl`, and returns an update `var_decl` and `disam_tbl`.

- process_symbol: `type_check_stmt_functs`'s copy of `Typing.process_symbol`, the function that type-checks a whole `Module.symbol` (used e.g. by `Rewriter.introduce_typecheck_symbol` and `ProgUtils.intros_type_module`, both of which take it as an argument for the same reason described below). It's handed to you as a plain function, already resolved -- you don't need to know that `Typing` itself can only make it available to code outside `typing.ml` via `Rewriter.process_symbol_ref`, a reference set exactly once, at the end of `typing.ml`, to work around the fact that `Rewriter` (in `lib/ast`) can't statically depend on `Typing` (in `lib/frontend`), and that `Typing.process_symbol` itself is defined later in the same file than some of the code that needs it. That reference isn't part of the extension API and isn't something you should need to touch.

- process_stmt: `type_check_stmt_functs`'s copy of (the relevant part of) `Typing.ProcessCallable.process_stmt`, the function that type-checks one statement of an ordinary callable body, recursing into `Block`/`Loop`/`Cond` and managing their scopes along the way. Only relevant to `type_check_stmt_ext` (see [Statement-bodied extensions](#statement-bodied-extensions-stmtext-at-the-stmt_desc-level)) -- `type_check_basic_stmt` never needs it, since a `basic_stmt_desc` can't embed a nested `Stmt.t` in the first place. Wired the same way `process_symbol` is, via a `Rewriter.process_stmt_ref` set once at the end of `typing.ml`, for the same dependency-direction reason; again, not something you touch directly.

### [AstDef](../../lib/ast/astDef.ml)

AstDef contains the main Raven syntax constructs, along with helper functions like printing, or building certain terms. Note that AstDef contains many pure functions which don't return `Rewriter.t` monads. One must be careful to make sure they use each function in the right way.

- Ident.fresh: Generates a fresh Ident, by appending a unique `ident_num` to a string. Always use this function when generating new idents to prevents collisions.

- QualIdent.to_loc: Takes a qual_ident and returns its corresponding `location`.

- Type.mk_prod: Takes a list of `type_expr` and returns a product type of all the types.

- Type.mk_fld: Takes a `type_expr`, and generates a type expression for a field of that type.

- Type.set_ghost_to: Updates a type expressions's _ghost_ status. This flag is used to ensure that ghost constructs are not used in non-ghost contexts.

- Type.bool: Returns the `type_expr` corresponding to Raven's `Bool` type.

- Expr.mk_var: Construct a `Var` expression. Takes a `type_expr` and a `qual_ident` and constructs a variable expression of the `qual_ident` with the `type_expr` type.

- Expr.mk_tuple: Takes a list of expressions and returns a `tuple` expression of all its arguments.

- Expr.signature: Returns a map of free variables occuring in an expression, with their types.

- Expr.alpha_renaming: Used to perform alpha-renaming on expressions. Takes an expression and a map from `qual_ident`s to `expr`s, and returns the alpha-renamed expression.

- Expr.existential_vars: Returns a map of existentially quantified variables in an expression, pointing to their types.

- Expr.supply_witnesses: Used to replace existentially quantified witnesses in an expression, with certain user-supplied "witnesses"

- Expr.mk_app: Used as a general constructor to create any expression.

- Expr.mk_and: Constructs a conjunction of a list of expressions passed as an argument.

- Expr.from_var_decl: Constructs an expression for a variable from its declaration.

- Expr.mk_binder: Used to construct existentially/universally quantified expressions.

- Stmt.mk_spec: It takes an expression and converts it into a "spec", or a specification. This is used to construct callable pre/post-conditions, and (see [Contracts](#contracts)) is a natural payload type for a `contract_ext` constructor.

- Stmt.mk_assume_expr: It takes an expression and converts it into an "assume" statement.

- Stmt.mk_assert_expr: Like `mk_assume_expr`, but for "assert" statements -- what actually gets checked. Give it a `~spec_error` (see `mk_const_spec_error` below) or the checker fails silently on a violation: `Error.fail_with` on an assert with an empty `spec_error` raises an exception carrying no error messages, which the top-level handler reports as nothing printed and a non-zero exit code.

- Stmt.mk_const_spec_error: Takes an `Error.t` (an `error_kind * Loc.t * string` triple) and wraps it into the `qual_ident -> Loc.t -> Error.t` shape `spec.spec_error` expects, ignoring both arguments -- use this when your message and location are already fully determined at the point you're building the spec, which is the common case. (`spec_error` is a *list* of such functions precisely so it can support cases where the message legitimately depends on which callable is being checked at report time -- see how `Rewrites.rewrite_stmt_error_msg`'s `Loop` case distinguishes "may not hold on loop entry" from "may not be maintained" for invariants.)

- Stmt.mk_block_stmt: It takes a list of statements and bundles these into one "block" statement.

### [Rewriter](../../lib/ast/rewriter.ml)

The Rewriter module mainly provides the monad which carries Raven's symbol table state thorugh the program. As a result, it also has functionality related to looking up symbol and introducing new symbols. 

One notion is that of "reified" declarations. In order to handle higher order module instantiations, when looking up symbols, Raven's SymbolTbl returns a tuple of the symbol, along with certain module name replacements that need to be done. Reifying the declaration implements these replacements and gives us a `Module.symbol` object.

- `Rewriter.current_scope_id`: Return the identifier of the current callable or module scope. Useful when generating fresh symbols tied to the active scope in order to build a fully qualified name.

- `Rewriter.current_module_name`: Return the name of the module currently being rewritten (in the `Rewriter` monad). Useful for creating module-scoped identifiers.

- `Rewriter.is_ghost_scope`: Function that returns whether the current scope is a ghost scope. Certain actions are allowed or disallowed in ghost contexts, so this is useful to distinguish.

- `Rewriter.enter_ghost`: Temporarily enter a "ghost" scope in Raven's symbol table state. This is used to mark for example ghost code-blocks in Raven denoted by `{! ... !}`. There is a corresponding `Rewriter.exit_ghost` that must be called when the ghost section is over.

- `Rewriter.resolve_and_find`: Resolve a qualified identifier (or name) in the current program context and, and also return the corresponding symbol information. This function returns a `qual_ident` denoting the fully qualified (ie not relative) name of the symbol, and also the symbol that the object refers to.

- `Rewriter.Symbol.reify`: Takes an object returned from a `find` function, performs any module substitutions if required, and returns the reified symbol.

- `Rewriter.Symbol.reify_field_type`: Similar to `Rewriter.reify` but makes sure the underlying symbol is a field declaration.

- `Rewriter.find_and_reify_var`: Does a similar thing as `Rewriter.resolve_and_find`, but also goes ahead and _reifies_ the symbol. This also makes sure the symbol is a `VarDef` and unfolds it. Otherwise this function raises an internal error. You should use this function to look up objects that you know are variables.

- `Rewriter.find_and_reify_callable`: Similar to `Rewriter.find_and_reify_var` but for callables.

- `Rewriter.introduce_symbol`: Insert a new symbol (variables, callables, types, modules, etc) into the current symbol table. This inserts the symbol in the "current" location in the symbol table.

- `Rewriter.introduce_typecheck_symbol`: This is similar to `Rewriter.introduce_symbol` but also performs type-checking on the defined symbol. It is almost always better to use this since it ensures type-safety of the newly introduced, and makes certain transformations like type-inference and type propagation. This function requires a `process_symbol`-shaped function as an argument -- pass the `process_symbol` field from `type_check_stmt_functs` if you have one in scope, or `!Rewriter.process_symbol_ref` (the reference `Typing.process_symbol` is installed into, once, at the end of `typing.ml`) otherwise.

- `Rewriter.current_ext_hooks`: Returns the full `ext_hooks` record installed for the active extension (see [Wiring](#wiring-how-ext_hooks-reaches-your-code)). You'll rarely need this directly -- Raven already applies the relevant `ext_hooks` field for you before calling into `type_check_*`/`rewrite_*_ext` -- but it's there if you need to delegate to another extension's hook explicitly.

- `Rewriter.current_printers`/`Rewriter.Logs`: See [Printing and logging from your extension](#printing-and-logging-from-your-extension) above -- use these instead of `AstDef.Type.pr`/`AstDef.Expr.pr`/`AstDef.Stmt.pr`/plain `Logs.debug` whenever you're printing or logging an AST fragment from inside your extension's code, so `*_ext` nodes belonging to other stacked extensions render correctly too.

The following are monadic implementations of commonly used higher order functions which are used when we want to use the higher order functions, but also want the monadic state available in the underlying functions.

- `Rewriter.List.fold_right`: Monadic `fold_right` implemented for lists inside the `Rewriter` monad; threads the rewriter state while folding.

- `Rewriter.List.map`: Monadic `map` for lists that applies a `Rewriter` computation to each element and returns the list of results in the `Rewriter` monad.

- `Rewriter.Option.map`: Monadic `map` for `option` values; applies a `Rewriter` computation when the option is `Some` and preserves `None`.

- `Rewriter.List.map2_exn`: Monadic version of `List.map2_exn` that maps a pair of lists with a function returning a `Rewriter` computation; raises on length mismatch.


## Wiring: how `ext_hooks` reaches your code

Every function you implement in your extension (`type_ext_to_name`, `type_check_basic_stmt`, `rewrite_expr_ext`, ...) has to be reachable from deep inside `lib/ast`'s and `lib/frontend`'s generic AST traversal, printing, and rewriting code -- code that runs identically regardless of which extension (if any) is active, and that cannot depend on `lib/ext` (extensions depend on the core, not the other way round). Raven resolves this by bundling all of the functions an extension implements into a single record, `Ast.Rewriter.ext_hooks` (defined in [rewriter.ml](../../lib/ast/rewriter.ml) alongside the `Rewriter.t` monad itself), and threading that record through the pipeline as an ordinary value:

1. [`bin/raven.ml`](../../bin/raven.ml) resolves the `--extension` flag to a `(module ExtApi.Ext)` via `Ext.module_map`, then converts it to an `ext_hooks` value via `Ext.to_ext_hooks` (in [ext.ml](../../lib/ext/ext.ml)) -- this is the *only* place a `module Ext : ExtApi.Ext` gets unpacked into plain data.
2. That `ext_hooks` value is passed as an explicit `~ext_hooks` argument into `Typing.process_module` and `Rewrites.process_module`, which install it into the `Rewriter.t` monad's state via `Rewriter.eval ?ext_hooks`.
3. From then on, any code running inside the `Rewriter.t` monad -- which is essentially all of type-checking and rewriting, including the code inside your own extension -- can read it back out with `Rewriter.current_printers` (for the printing/query functions) or by pattern-matching `Ast.Rewriter.ext_hooks`'s other fields directly. Extension code practically never needs to do this itself, since Raven only calls into `type_check_type_expr`/`rewrite_stmt_ext`/etc. *with* the relevant pieces of `ext_hooks` already applied (e.g. via the `type_check_*_functs` bundles, see [Typing](#typing) above) -- but it matters if your own implementation wants to print or log an AST fragment that might still contain another extension's constructs (see [Printing and logging from your extension](#printing-and-logging-from-your-extension)).

