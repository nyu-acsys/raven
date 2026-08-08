  $ dune exec -- raven --shh ./reset.rav
  [Error] File "./reset.rav", line 10, columns 1-1:
  10 | }
        ^
  Verification Error: A postcondition may not hold at this return point.
  [Error] File "./reset.rav", line 7, columns 10-25:
  7 |   ensures own(c.count, 0)
                ^^^^^^^^^^^^^^^
  Related Location: This own predicate may not hold.
  [1]
