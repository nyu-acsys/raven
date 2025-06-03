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
- reorder rewrite passes to do inj checks for preds before rewriting fold/unfold
    + maybe by adding new lemmas
- sweep to add default triggers for every Quant
    + fix missing triggers in all `Expr.mk_binder` calls

- [x] add forks
- toy around with preds as macros



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

- [x] Fix `return proc()` stmts
- [x] Allow parsing of `map[m1][m2]` expressions
    (Thomas did implement a fix for this, but needs review)

- Parse field reads/writes/cas/fpu separately
- Allow types to be used as modules implementing Library.Type



===

- [x] Fix dependency analysis wrt auto lemmas
- [x] Investigate spurious "unknown"s in the middle of log files