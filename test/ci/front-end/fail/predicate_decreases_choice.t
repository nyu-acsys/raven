  $ dune exec -- raven --shh ./predicate_decreases_choice.rav
  [Error] File "./predicate_decreases_choice.rav", line 4, columns 12-16:
  4 |   decreases p(x)
                  ^^^^
  Type Error: structural predicate measures require recursive arguments and guards to be determined by parameters, equalities, or full field ownership.
  [1]
