  $ dune exec -- raven --shh ./sum_counter.rav
  [Error] File "./sum_counter.rav", line 100, columns 3-3:
  100 |   }
           ^
  Verification Error: A postcondition may not hold at this return point.
  [Error] File "./sum_counter.rav", line 97, columns 12-27:
  97 |     ensures valid(s, v + 1)
                   ^^^^^^^^^^^^^^^
  Related Location: This predicate may not hold.
  [1]
