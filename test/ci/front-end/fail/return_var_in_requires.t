  $ dune exec -- raven --shh ./return_var_in_requires.rav
  [Error] File "./return_var_in_requires.rav", line 5, columns 11-12:
  5 |   requires r > 0
                 ^
  Type Error: Return variable r cannot be used in a requires clause; it is only in scope in ensures clauses.
  [1]
