  $ dune exec -- raven --shh ./gcd.rav
  [Error] File "./gcd.rav", line 21, columns 1-1:
  21 | }
        ^
  Verification Error: A postcondition may not hold at this return point.
  [Error] File "./gcd.rav", line 7, columns 10-15:
  7 |   ensures r > 0 && r <= a && r <= b
                ^^^^^
  Related Location: This assertion may not hold.
  [1]
