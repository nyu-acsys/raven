  $ dune exec -- raven --shh ./shelf_growth.rav
  [Error] File "./shelf_growth.rav", line 39, columns 1-1:
  39 | }
        ^
  Verification Error: A postcondition may not hold at this return point.
  [Error] File "./shelf_growth.rav", line 35, columns 10-31:
  35 |   ensures shelfList(hd2, n + 1)
                 ^^^^^^^^^^^^^^^^^^^^^
  Related Location: This predicate may not hold.
  [1]
