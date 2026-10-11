  $ dune exec -- raven --shh ./predicate_decreases_precondition.rav
  [Error] File "./predicate_decreases_precondition.rav", line 3, columns 12-16:
  3 |   decreases p(n)
                  ^^^^
  Type Error: a predicate decreases measure must occur exactly once as a top-level chunk of the precondition.
  [1]
