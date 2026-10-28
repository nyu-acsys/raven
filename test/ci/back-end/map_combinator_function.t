  $ dune exec -- raven --shh map_combinator_function.rav
  [Error] File "map_combinator_function.rav", line 48, columns 2-2:
  48 | {}
         ^
  Verification Error: A postcondition may not hold at this return point.
  [Error] File "map_combinator_function.rav", line 47, columns 10-24:
  47 |   ensures included(a, b)
                 ^^^^^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]
