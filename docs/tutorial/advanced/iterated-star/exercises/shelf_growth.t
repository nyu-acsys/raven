  $ dune exec -- raven --shh ./shelf_growth.rav
  [Error] File "./shelf_growth.rav", line 40, columns 1-1:
  40 | }
        ^
  Verification Error: A postcondition may not hold at this return point.
  [Error] File "./shelf_growth.rav", line 36, columns 10-31:
  36 |   ensures shelfList(hd2, n + 1)
                 ^^^^^^^^^^^^^^^^^^^^^
  Related Location: This predicate may not hold.
  [1]
