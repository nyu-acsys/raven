  $ dune exec -- raven --shh ./sum_range.rav
  [Error] File "./sum_range.rav", line 17, columns 1-1:
  17 | }
        ^
  Verification Error: A postcondition may not hold at this return point.
  [Error] File "./sum_range.rav", line 7, columns 10-30:
  7 |   ensures 2 * r == n * (n + 1)
                ^^^^^^^^^^^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]
