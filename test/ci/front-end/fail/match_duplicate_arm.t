  $ dune exec -- raven --shh ./match_duplicate_arm.rav
  [Error] File "./match_duplicate_arm.rav", line 8, column 2 to line 12, column 3:
  8 |   match x {
        ^^^^^^^^^
  Type Error: constructor 'nil' is matched by more than one arm.
  [1]
