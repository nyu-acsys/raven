  $ dune exec -- raven --shh ./match_bad_arms.rav
  [Error] File "./match_bad_arms.rav", line 10, column 2 to line 14, column 3:
  10 |   match x {
         ^^^^^^^^^
  Type Error: 'one' expects 1 pattern variable(s), but this arm binds 2.
  [1]
