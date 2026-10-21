# Coding conventions

Here are some coding conventions that we should adhere to (in random order).

* Reserve the use of exceptions for cases where program execution should be aborted. That is, `try ... with` blocks are confined to the very top-level error handling functions, in `bin/raven.ml` and in `Raven_api.verify` for the clients of `raven.api`, and the error combinators of the `Rewriter` monad (`Rewriter.eval`, `Rewriter.map_errors` and the recovery point `Rewriter.recover`). Use `Option.t` and friends instead of exceptions in other cases. Learn about monads/applicatives if you want nice syntax.

* Do not write directly to standard output / standard error. Use the [Logs](https://erratique.ch/software/logs) module.

* Use `begin ... end` blocks instead of `( ... )` whenever it improves code readability (e.g. for nested `match` expressions).

* When the code of a lambda abstraction that is passed to a higher-order function spans many lines, replace it by an appropriately named function.

* Avoid code duplication. When you are tempted to copy a large chunk of code, don't be lazy. Refactor it into a new function.

* Try to keep error handling local. Instead of writing code like this:

  ```ocaml
  (match ... with
  | pattern(val) -> (* do a long complex computation with val *)
  | ... | ... | -> a bunch of error cases)
  ```

  write it like this:

  ```ocaml
  let val = match ... with
  | pattern(val) -> val
  | ... | ... | -> a bunch of error cases
  in 
  (* do a long complex computation with val *)
  ```
  
  This increases the readability of the code.