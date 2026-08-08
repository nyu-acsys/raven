  $ dune exec -- raven --shh ./swap.rav
  [Error] File "./swap.rav", line 11, columns 1-1:
  11 | }
        ^
  Verification Error: A postcondition may not hold at this return point.
  [Error] File "./swap.rav", line 8, columns 10-27:
  8 |   ensures own(c1.count, v2) && own(c2.count, v1)
                ^^^^^^^^^^^^^^^^^
  Related Location: This own predicate may not hold.
  [1]
