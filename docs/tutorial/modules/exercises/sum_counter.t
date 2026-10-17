  $ dune exec -- raven --shh ./sum_counter.rav
  [Error] File "./sum_counter.rav", line 100, columns 3-3:
  100 |   }
           ^
  Verification Error: A postcondition may not hold at this return point.
  [Error] File "./sum_counter.rav", line 97, columns 12-27:
  97 |     ensures valid(s, v + 1)
                   ^^^^^^^^^^^^^^^
  Related Location: This predicate may not hold.
  [Error] File "./sum_counter.rav", line 108, columns 3-3:
  108 |   }
           ^
  Verification Error: A postcondition may not hold at this return point.
  [Error] File "./sum_counter.rav", line 104, columns 27-33:
  104 |     ensures valid(s, v) && r == v
                                   ^^^^^^
  Related Location: This assertion may not hold.
  [Error] File "./sum_counter.rav", line 115, columns 3-3:
  115 |   }
           ^
  Verification Error: A postcondition may not hold at this return point.
  [Error] File "./sum_counter.rav", line 112, columns 27-33:
  112 |     ensures valid(s, v) && v >= 0
                                   ^^^^^^
  Related Location: This assertion may not hold.
  [1]
