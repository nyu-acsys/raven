  $ dune exec -- raven --shh match_stmt_fail.rav
  [Error] File "match_stmt_fail.rav", line 14, columns 1-1:
  14 | }
        ^
  Verification Error: A postcondition may not hold at this return point.
  [Error] File "match_stmt_fail.rav", line 8, columns 10-16:
  8 |   ensures a >= 0
                ^^^^^^
  Related Location: This assertion may not hold.
  [1]
