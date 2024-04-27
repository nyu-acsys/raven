  $ dune exec -- ../../bin/raven.exe --shh ./simple.rav
  [Error] File "./simple.rav", line 13, columns 1-1:
  13 | }
        ^
  Verification Error: A postcondition may not hold at this return point.
  [Error] File "./simple.rav", line 9, columns 10-16:
  9 |   ensures x == 5
                ^^^^^^
  Related Location: This is the postcondition that may not hold.
  [1]
