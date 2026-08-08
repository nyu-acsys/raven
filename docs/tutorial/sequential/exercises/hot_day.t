  $ dune exec -- raven --shh ./hot_day.rav
  [Error] File "./hot_day.rav", line 21, columns 1-1:
  21 | }
        ^
  Verification Error: A postcondition may not hold at this return point.
  [Error] File "./hot_day.rav", line 9, columns 67-75:
  9 |   ensures forall j: Int :: {counts[j]} 0 <= j && j < len ==> counts[j] <= r
                                                                         ^^^^^^^^
  Related Location: This assertion may not hold.
  [1]
