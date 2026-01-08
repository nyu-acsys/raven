# Raven's Extension API

This file contains a thorough documentation of Raven's Extension API. It is intended as a starting point for a verification expert, hereafter referred to as the _programmer_, to be able to add their own features to Raven by implementing their own extensions. For this purpose, not only does this document describe the API in detail, it also contains pointers to parts of several OCaml code files where relevant Raven functionality is implemented.


## Overview

Raven's Extension API is designed to allow a programmer to rapidly adapt Raven's front-end language for specific use-cases, without having to wade into Raven's entire existing pipeline. The programmer can define custom types, expressions, and statements that they want to be added to Raven. 

We make use of OCaml's extensible variant types to expose types to the programmer which tie into the core AST representations for Raven's types, expressions, and statements. These types are `AstDef.Type.type_ext`, `AstDef.Expr.expr_ext`, and `AstDef.Stmt.stmt_ext` defined in `lib/ast/astDef.ml`, which allow the programmer to extend types, expressions, and statements respectively.

To make an extension, broadly speaking, the programmer needs to implement a module satisfying the `ExtApi.Ext` API. These modules have a signature like so:
```
module SampleExt (Cont: ExtApi.Ext) : ExtApi.Ext
```

These are higher-order modules that accept, as a parameter, another extension module implementing the `ExtApi.Ext` interface. This allows us to "stack" these extensions on top of each other, and conveniently adjust the exact set of features we want to support when we compile Raven. This happens in `lib/ext/ext.ml`.


## Creating a New Extension

An extension typically consists of 3 files, and may contain a 4th file. For a new extension say `SampleExt`, these files are:

1. `sampleExt.ml`: This file contains the `SampleExt` module that satisfies the `ExtApi.Ext` API. This contains, at a high level, the declarations of the additional AST constructs, along with functions to type-check these constructs, as well as _rewrite_ these constructs into simpler Raven terms.

2. `sampleExt_parser.mly`: This file contains the parser rules for the new syntax that the extension needs. These rules are then combined with Raven's existing parser and compiled by Menhir. Raven's parser makes certain non-terminals public, which means they can be referenced from outside files. These terminals can then be extended using other public terminals, and other freshly defined tokens.

3. `dune`: This file is for the `dune` build system. It defines the current module along with dependencies so that the `dune` build system can compile the code. This file declares the name of the module, ensure that it is equal to `SampleExt`. 

4. (Optional) `sampleExt_lib.rav`: This file contains optional Raven code with Raven declarations relevant for implementing the extension. This file is included as part of Raven's standard library when compiling Raven. This allows the programmer to include certain Raven definitions for modules, interfaces, procedures, functions, types, etc that can then be used for example during the rewriting process in `sampleExt.ml`.

The best way to get started with a new extension is to copy an existing extension and clear out the existing functionality. There is also the `blank_ext.ml.md` file provided in the `ext` folder to serve as a quick-start for new extensions.


## Activating a New Extension

Once the programmer has created the extension such that it successfully compiles with the `dune build` command, they must complete the following steps to make sure the extension is integrated into the Raven pipeline and becomes usable:

1. In [lib/ext/dune](dune): 
  add the extension as a dependency by appending `sampleExt` to the `libraries` field of the `library` stanza (line 3).

2. In [lib/frontend/dune](../frontend/dune):
  a. add the extension as a dependency by appending `sampleExt` to the `libraries` field of the `library` stanza (line 3).

  b. add a rule to copy the `sampleExt_parser.mly` file into the `lib/frontend` directory. Like this:
  ```dune
    (rule
    (target sampleExt_parser.mly)
    (deps ../ext/sampleExt/sampleExt_parser.mly)
    (action (copy %{deps} %{target})))
  ```

  c. append `sampleExt_parser` to the `modules` field of the `menhir` stanza.

3. In [lib/frontend/terminals.ml](../frontend/terminals.ml), add any new keywords required by the extension. These correspond to the new tokens declared in `sampleExt_parser.mly`.

4. Finally, in [lib/ext/ext.ml](ext.ml):
  a. add a new module `SampleExtInstance` that instantiates `SampleExt` with an existing extension and introduce it into the chain of extensions. Typically, newer extensions should be added towards the end as the "outermost" instantiations.
  b. update the definition of `module Ext: ExtApi.Ext` to refer to the new instance `SampleExtInstance`.

5. Run `dune build; dune install` to compile Raven with the new extension.

That's it! 
- With the updated parser, Raven front-end will support the newly defined syntax.
- With the definition of the `Ext` module updated, Raven utilizes the new extension constructs while processing the input program.


## ExtApi - The extension API

In this section we describe the API that the programmer must implement in order to build an extension.

Any module for an extension implementing the API starts with declarations introducing new branches for some or all of `Type.type_ext`, `Expr.expr_ext`, or `Stmt.stmt_ext` types, thereby extending Raven's syntax by introducing new types, expressions, and statements, respectively. 

As a running example, let us consider that we want to add a new statement `randEven(n)` which denotes randomly sampling an _even_ number from 0 to n-1.

So, one would introduce a new kind of statement as follows:

```
type Stmt.stmt_ext +=
  | RandEven
```

This constructor directly extends Raven's AST with a new statement type. Note that we do not indicate any arguments for the new statement. In Raven, each statement is combined with an expression array of arguments.

While developing the extension, the general principle is that whenever an extension matches on the corresponding types `typeExt, exprExt, and stmt_ext`, it should handle all the cases of the constructor that are defined in this file, and include a catch-all case which calls the corresponding functionality from the `Cont` module. Here is an example:

```ocaml
  let stmt_ext_symbols stmt_ext =
    match stmt_ext with
    | RandEven -> 
      (* Handle the RandEven case *)
      Set.empty (module QualIdent)
    | _ -> 
      (* Defer to the continuation for any other case *)
      Cont.stmt_ext_symbols stmt_ext
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

Please take a look at [sampleExt.ml](sampleExt/sampleExt.ml) and [dune](sampleExt/dune) for an example of how to include an optional library file.

- `val local_vars : var_decl list`
This value contains a list of variables that the extension depends on, which can be blank if no such variables are needed. These variables are added as local variables to every procedure in the program, so that these can be reliably used during rewriting to encode the new constructs.

Please see [errorCreditsExt.ml](errorCreditsExt/errorCreditsExt.ml) for an example of how to declare a local variable.

### AstDef

The API contains the following functions in the AstDef section:

```ocaml
  val type_ext_to_name : (Type.type_ext -> string)

  val expr_ext_to_string : (Expr.expr_ext -> string)

  val pr_stmt_ext : Stdlib.Format.formatter -> Stmt.stmt_ext -> expr list -> unit

  val stmt_ext_symbols: Stmt.stmt_ext -> QualIdentSet.t
  val stmt_ext_local_vars_modified : Stmt.stmt_ext -> expr list -> ident list
  val stmt_ext_fields_accessed : Stmt.stmt_ext -> expr list -> qual_ident list
```

These functions are used in Raven's AST to be able to print the new constructs, or collect certain information about statements, such as local variables and fields accessed.

In each of these functions, the programmer is expected to case match on the corresponding extension argument (type_ext/expr_ext/stmt_ext), and match for all the cases that are declared in this extension. For any unknown case, the extension is required to defer to the remaining extensions by calling the same functionality from the `Cont` module.

If a construct category is not modified in the extension, then these functions can also be directly defined from `Cont`, for example:
```ocaml
  let type_ext_to_name = Cont.type_ext_to_name
  let expr_ext_to_string = Cont.expr_ext_to_string
```

The `pr_stmt_ext` command takes a `stmt_ext` and `expr_list`, a list of expressions. The programmer is supposed to fill in how to print this statement. Certain assumptions can be made about the number and types of arguments in `expr_list`; these are usually guaranteed by type-checking or the parser. The programmer can thus throw internal errors if this is violated, as seen in [sampleExt.ml](sampleExt/sampleExt.ml).

The `stmt_ext_symbols` is a function that is almost always expected to return `Set.empty (module QualIdent)`, but included for future expansion.

The `stmt_ext_local_vars_modified` and `stmt_ext_fields_accessed` are two functions with which the programmer lets Raven know what variables to refresh and what fields to model when encoding the program into logical constraints. These functions have a return type of `ident list` and `qual_ident list` respectively, and are expected to return which local variables and fields are updated by a specific command. In [sampleExt.ml](sampleExt/sampleExt.ml) we see the use of `Expr.to_qual_ident`, `QualIdent.is_local` and `QualIdent.to_ident` functions. These are all implemented in `lib/ast/astDef.ml`, and discussed more thoroughly in [Userful Functions](#useful-functions). 

In `stmt_ext_local_vars_modified`, we return the `lhs_expr` converted to an ident if it is "local", ie, does not refer to a global variable, and importantly does not have module qualifiers in its `qual_ident`. Otherwise we return `[]`. In `stmt_ext_fields_accessed` we return `[]` always.

### Rewriter

This API contains the following functions which are used by Raven to perform any _type_ rewrites on the extensions if necessary:

```ocaml
  val expr_ext_rewrite_types :
    f:(type_expr -> type_expr Rewriter.t)
    -> Expr.expr_ext 
    -> Expr.expr_ext Rewriter.t

  val stmt_ext_rewrite_types :
    f: (type_expr -> type_expr Rewriter.t) 
    -> Stmt.stmt_ext 
    -> Stmt.stmt_ext Rewriter.t
```

These are only required if the expression or statement extensions defined in this extension store types. Please take a look at [prophecyExt](prophecyExt/prophecyExt.ml) to see a non-trivial example implementation of these functions.

In [sampleExt.ml](sampleExt/sampleExt.ml), we simply skip these functions, setting them equal to the one from `Cont`.

### Typing

This API contains the following functions which are used by Raven to type-check any newly defined types, expressions and statements:

```ocaml
  val type_check_type_expr : Type.type_ext -> type_expr list -> Type.type_attr -> type_check_type_expr_functs -> type_expr Rewriter.t

  val type_check_expr : Expr.expr_ext -> expr list -> Expr.expr_attr -> type_expr -> type_check_expr_functs -> expr Rewriter.t

  val type_check_stmt : 
    Callable.call_decl ->
    Stmt.stmt_ext -> expr list ->
    location ->
    ProgUtils.DisambiguationTbl.t ->
    type_check_stmt_functs ->
    (Stmt.basic_stmt_desc * ProgUtils.DisambiguationTbl.t) Rewriter.t
```

These type signatures are a bit more complicated. Let's go through them one at a time.

For `type_check_type_expr`:
- It takes the `type_ext` and the `type_expr list` as arguments. These constitute the definition of the new type. 

- The `type_attr`, defined in [astDef.ml](../ast/astDef.ml) refers to _type attribute_, which contains a _location_ as well as ghost status. This location is tied to input location which is used to show to the user the relevant pieces of code for a given error. 

- The next argument is of type `type_check_type_expr_functs` (defined in [extApi.ml](api/extApi.ml)) which is a record object storing a set of functions that are useful during type-checking `type_expr`s. At present, this only contains the `process_type_expr` function which is originally defined in [typing.ml](../frontend/typing.ml). This function is used to process any sub-expressions during the processing of the current type_expr. 

- Finally, it has a return type of `type_expr Rewriter.t`. `Rewriter.t`, defined in [rewriter.ml](../ast/rewriter.ml), is a monad that carries Raven's symbol table state throughout the program, letting us do things like seamlessly look up symbol definitions from the program. We use the `let*` and `let+` bindings from `Rewriter.Syntax` in order to interact with this monad. We also use the `Rewriter.return` to wrap a normal value into the monad. In general, keeping the monad in mind is very useful, specially with higher-order functions. The Rewriter module contains its own implementations for commonly used functions such as `List.map`, and `List.fold_right`, implemented in [state.ml](../util/state.ml).

Here, `type_expr Rewriter.t` refers to the fact that this function returns a `type_expr`, wrapped inside the `Rewriter` monad.

Similarly, for `type_check_expr`:
- It takes the `expr_ext` and `expr list` as arguments, which constitute the new expression.

- The `expr_attr` defined in [astDef.ml](../ast/astDef.ml) refers to _expression attributes_, which contain a location as well as the expression's _type_.

- The next argument of type `type_expr` is the _expected type_ of the expression being type-checked. This is often `Type.Any`, but can include typing hints from the environment.

- The next argument, of type `type_check_expr_functs`. This is the set of functions from [typing.ml](../frontend/typing.ml) that are useful while type-checking expressions. Please refer to [Useful Functions](#useful-functions) to identify how to use each of these functions.

As for `type_check_stmt`, the goal of this function is to make sure the statement is well-formed with well-typed arguments. It has a considerably more complex type signature. In particular, it has a `call_decl` that contains information about the parent callable of this `stmt_ext`. It also contains a `ProgUtils.DisambiguationTbl.t`, which is a local, per-callable data-structure used to disambiguate local variables, for instance using the same variable in multiple different scopes. This procedure also returns a _disambiguation table_ which contains any updates made during type-checking the present statement. As usual, `type_check_stmt_functs` contains a list of useful functions. Notably, `disambiguate_process_expr` and `disam_tbl_add_var_decl` makes use of, and updates the disambiguation table respectively.

In [sampleExt.ml](sampleExt/sampleExt.ml), we first case-match on `RandEven`. For a sample statement like
  `x := randEven(n);`,
this gets parsed with `lhs_expr` denoting `x` and `n_expr` denoting `n`.

We use a function from `type_check_stmt_functs` to get the variable declaration for the `lhs_expr`. Once we get its `var_type`, we check to make sure it is an `Int` type, otherwise we throw a `type_mismatch_error`. Then we typecheck `n_expr` using `Type.int` or `Int` as the expected type. At this point we are ready to return the updated statement, constructed with the `Stmt.StmtExt` constructor denoting an extension statement, along with `disam_tbl`. 

If the arguments are not what we expect, then we throw a type error straightaway. And if it is an unknown constructor, then we defer to the continuation extension `Cont`, as usual.


### Rewrites

This section contains functions that perform essential rewrites to reduce the newly extended front-end features into built-in Raven constructs.


```ocaml
  val rewrite_type_ext : Ast.Type.type_ext -> type_expr list -> location -> type_expr Rewriter.t

  val rewrite_expr_ext : Expr.expr_ext -> expr list -> Expr.expr_attr -> expr Rewriter.t
  
  val rewrite_stmt_ext : Stmt.stmt_ext -> expr list -> location -> Stmt.t Rewriter.t
```

These functions are more straight-forward to follow. Essentially for each new construct, we return an equivalent encoding of the data structure in "native" Raven. For instance, expressions can be translated into different expressions involving functions and heap expressions. Statements can be rewritten into equivalent set of statements, combined into one `Stmt.Block` stmt, often involving `inhale` and `exhale` statements, or field reads/writes, etc.

In [sampleExt.ml](sampleExt/sampleExt.ml), we introduce one `havoc` statement, to havoc the value of the lhs expression, and then inhale a statement expressing constraints about the newly-assigned value.


### Epilogue

This contains values that properly propate and acculumate the configurations from successive extensions. There is usually no need to modify these values, which is why this section carries a warning in the comments.

```ocaml
  val lib_sources : (string * string) list
  val ext_local_vars : var_decl list
```

This sums up the API itself. In the next section we will discuss many commonly used functions in the Raven code-base, and other relevant code in order to provide a starting point into the code-base. At present, the best way to understand how to use each of these functionalities is to read the code, find references to specific functions and see how they're being used. Please contact the authors if you're interested, we will be happy to give a walkthrough, discuss specific extension designs, and answer any questions you may have.

<!-- We will try our best to add documentation and comments to extensions and the code-base in general. -->


## Useful Functions

In order to correctly implement the right type-checking and rewrite strategies, certain Raven functionality is invaluable. In order to orient a new programmer with the different functionalities, where they are located, and best practices when creating an extension, we provide an overview of certain commonly-used functions and how the rest of the code is organized. Here is a list of notable functions from different sections:

### Typing

process_type_expr

check_and_set
process_expr
type_mismatch_error

get_assign_lhs
expand_type_expr
disambiguate_process_expr
type_mismatch_error
disam_tbl_add_var_decl
process_symbol_ref

### AstDef

Ident.fresh

QualIdent.to_loc

Type.mk_prod
Type.mk_fld
Type.set_ghost_to
Type.bool

Expr.mk_var
Expr.mk_tuple
Expr.signature
Expr.alpha_renaming
Expr.existential_vars
Expr.supply_witnesses
Expr.mk_app
Expr.mk_and
Expr.from_var_decl
Expr.mk_binder

Stmt.mk_spec
Stmt.mk_assume_expr
Stmt.mk_block_stmt

### Rewriter

Rewriter.current_scope_id (find current callable)
Rewriter.resolve_and_find
Rewriter.introduce_symbol
Rewriter.find_and_reify_var
Rewriter.find_and_reify_callable
Rewriter.resolve_and_find
Rewriter.Symbol.reify
Rewriter.is_ghost_scope
Rewriter.enter_ghost
Rewriter.Symbol.reify_field_type

Rewriter.List.fold_right
Rewriter.List.map
Rewriter.Option.map
Rewriter.List.map2_exn

Rewriter.current_module_name
Rewriter.introduce_typecheck_symbol
Rewriter.introduce_symbol