  $ dune exec -- raven --shh ./double_ownership.rav
  [Error] File "./double_ownership.rav", line 20, columns 1-1:
  20 | }
        ^
  Verification Error: A postcondition may not hold at this return point.
  [Error] File "./double_ownership.rav", line 18, columns 29-44:
  18 |   ensures own(c.count, v) && own(c.count, v)
                                    ^^^^^^^^^^^^^^^
  Related Location: This own predicate may not hold.
  [1]
