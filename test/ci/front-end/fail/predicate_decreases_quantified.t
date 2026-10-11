  $ dune exec -- raven --shh ./predicate_decreases_quantified.rav
  [Error] File "./predicate_decreases_quantified.rav", line 4, columns 12-16:
  4 |   decreases p(x)
                  ^^^^
  Type Error: structural descent through universally quantified resource chunks is not supported.
  [1]
