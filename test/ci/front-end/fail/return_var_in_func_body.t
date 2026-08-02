  $ dune exec -- raven --shh ./return_var_in_func_body.rav
  [Error] File "./return_var_in_func_body.rav", line 6, columns 2-5:
  6 |   res
        ^^^
  Type Error: Return variable res cannot be used in the body of f; it is only in scope in ensures clauses.
  [1]
