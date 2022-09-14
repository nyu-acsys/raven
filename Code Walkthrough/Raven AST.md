Raven Abstract Syntax Tree (AST) is defined at `/lib/ast/ast.ml`
Raven has 7 types of constructs in the language. Each construct is implemented in a separate module in the AST, laid out in a logical order based on dependencies. Each module implements not only the types and related constructs to represent their corresponding objects, but also has several helper functions to print stuff, access and set different fields, helper types, etc.

1. Identifiers (`Ident`): An identifier consists of a name and a number. Ident `{x, 5}` is represented as `x#5`. The number defaults to zero if absent (`x == x#0`).
   The number is used to generate unique identifiers.
   
2. Qualified Identifiers (`QualIdent`): Qualified identifier is an identifier accompanied by a path. Used to identify objects in different namespaces (modules). Eg `Lock.bit`.
   
3. Types (`Type`): There are several built-in types like `Int`, `Bool`, `Unit`, `Ref`, `Perm`, `Bot`, `Any` etc, 
   
%% [[Raven Questions]]: Do we want to have `Any` and `Bot` as part of semantics as well? Or are they to be used only internally while type-inferring and type-checking?%%
   
   as well as constructors for more complex types like `Set`, `Map`, `Data`, `AtomicToken` and arbitrary named types with `Var`. Each Type consists of a type constructor and a list of type arguments. For built-in types, the type-argument list is required to be empty.
   
   The Type module also defines other related constructs like `var_decl` which stores information about a declared variable, and `variant_decl` which is used to construct algebraic data types (see `Data` type constructor)
   
4. Expressions (`Expr`): Similarly, expressions consist of a expression constructor and list of expression arguments. Constructors for expressions comprise of everything from boolean operators, arithmetic operators, set operations, variables, etc.
   
5. Statements (`Stmt`): Stmt module defines a list of basic statements (`basic_stmt_desc`). A statement consists of either
	- a list of statements (`block`)
	- a `basic_stmt_desc`
	- a loop; it contains a loop invariant, pre-body, loop condition and body
%% [[Raven Questions]]: Understand why we need a pre-body exactly %%
   
6. Functions & Methods (`Callable`): Different callables, including Procedures, Lemmas, Functions, Predicates and Invariants are implemented uniformly using the `Callable` interface. A `Callable` consists of a call_kind, name, parameters, pre/post condition, return values
 %% [[Raven Questions]]: Get comfortable with specifying return values up front. I'm still a little iffy on what code like that would look like. %%
   
7. Modules (`Module`): Modules are also implemented as records which store a *module declaration* and *module definition*. 
   
	The module declaration consists of:
	- module name
	- constructor arguments
	- return type
	%% [[Raven Questions]] what exactly are modules returning? %%
	
	-  rep type
	- declared fields
	- declared modules and aliases
	- declared types
	- declared callables
	- declared variables

	The module definition consists of a list of members. Each member could be:
	- type alias
	- import directive
	- module definition
	- field definition
	- variable definition
	- function definition

