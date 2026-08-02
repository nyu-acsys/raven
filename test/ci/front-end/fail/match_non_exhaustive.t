  $ dune exec -- raven --shh ./match_non_exhaustive.rav
  [Error] File "./match_non_exhaustive.rav", line 9, column 2 to line 12, column 3:
  9 |   match x {
        ^^^^^^^^^
  Type Error: non-exhaustive match: missing case(s) for cons.
  [1]
