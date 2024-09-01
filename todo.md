Type-checking:
  - Ensure that return variables are not allowed in pre-conditions
  - Check that openAU, commitAU having right number of arguments
  - Check that assertion expressions having the right format -- conditionals in ternary expr being pure, etc
  - Ensure that return variables of functions are not used in the function body
  - Ensure that predicates don't have implicit ghost args
  - Ensure that left-hand side of bindAU is well-typed (number of vars matches number of implicit args; types match, etc.) 

- Implement mask computation to check interface <-> module compatibility
- Improve expression matching algorithm
- Revamp witness computation code

- Fix `return proc()` stmts
- Allow parsing of `map[m1][m2]` expressions

- Parse field reads/writes/cas/fpu separately
- Fix dependency analysis wrt auto lemmas
- Investigate spurious "unknown"s in the middle of log files

- Fix missing triggers in all `Expr.mk_binder` calls

- Allow types to be used as modules implementing Library.Type