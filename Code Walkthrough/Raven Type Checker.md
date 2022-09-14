/lib/frontend/type_checker.ml

Entry-point: 
`start_type_check : Module.t -> Module.t * SymbolTbl.t`

## Purpose
Typechecker currently implements the following functionality:
- Take the disambiguated AST for a program and make sure that each variable is well-typed.
- Make sure each function/procedure (ie each `callable`) is called with arguments of the right arity and types.
- Make sure each module invocation is called with the right number of arguments
- All the module aliases are initialized with the correct number of arguments.

The structure of this file is similar to [[Raven Resolve Namespaces]]. There is a `SymbolTbl` module. This time a SymbolTbl consists of a stack of maps from identifiers to `typing_env` which can be one of `type_expr`, `Callable.call_decl`, `Module.module_alias`, `Module.module_decl`, `var_decl` or `Module.field_def`.

This is all the information the program needs to remember to be able to make sure that everything is well-typed.

After the symbolTbl, similar to [[Raven Resolve Namespaces]], the file is broken into modules for each language construct. However, since identifiers have been disambiguated, type checking does not need to deal with identifiers. Hence, we have the following 5 modules:
- `TypeTypeCheck`
- `ExprTypeCheck`
- `StmtTypeCheck`
- `CallableTypeCheck`
- `ModuleTypeCheck`