  $ dune exec -- raven --shh ./match_wildcard_not_last.rav
  [Error] File "./match_wildcard_not_last.rav", line 8, column 2 to line 11, column 3:
  8 |   match x {
        ^^^^^^^^^
  Type Error: a wildcard ('_') match arm must be the last arm.
  [1]
