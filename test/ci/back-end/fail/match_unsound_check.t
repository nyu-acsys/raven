  $ dune exec -- raven --shh ./match_unsound_check.rav
  [Error] File "./match_unsound_check.rav", line 20, columns 1-1:
  20 | }
        ^
  Verification Error: A postcondition may not hold at this return point.
  [Error] File "./match_unsound_check.rav", line 18, columns 10-21:
  18 |   ensures sel(x) == 0
                 ^^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]
