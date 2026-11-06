  $ dune exec -- raven --shh ./inline_predicate_match_shadow.rav
  [Error] File "./inline_predicate_match_shadow.rav", line 17, columns 1-1:
  17 | }
        ^
  Verification Error: A postcondition may not hold at this return point.
  [Error] File "./inline_predicate_match_shadow.rav", line 15, columns 10-15:
  15 |   ensures false
                 ^^^^^
  Related Location: This assertion may not hold.
  [Error] File "./inline_predicate_match_shadow.rav", line 31, columns 1-1:
  31 | }
        ^
  Verification Error: A postcondition may not hold at this return point.
  [Error] File "./inline_predicate_match_shadow.rav", line 23, columns 24-41:
  23 |     case next(value) => value == expected
                               ^^^^^^^^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]
