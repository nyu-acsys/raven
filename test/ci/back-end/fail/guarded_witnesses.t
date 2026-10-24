  $ dune exec -- raven --shh ./guarded_witnesses.rav
  [Error] File "./guarded_witnesses.rav", line 13, columns 2-26:
  13 |   fold wrong(cell, false);
         ^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: Failed to fold predicate. The body of the predicate may not hold at this point.
  [Error] File "./guarded_witnesses.rav", line 7, columns 26-45:
  7 |     (exists child: Int :: result == child + 1 && child == 8 && own(cell.value, child))
                                ^^^^^^^^^^^^^^^^^^^
  Related Location: This assertion may not hold.
  [Error] File "./guarded_witnesses.rav", line 7, columns 49-59:
  7 |     (exists child: Int :: result == child + 1 && child == 8 && own(cell.value, child))
                                                       ^^^^^^^^^^
  Related Location: This assertion may not hold.
  [Error] File "./guarded_witnesses.rav", line 25, columns 2-28:
  25 |   fold missing(cell, false);
         ^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: Failed to fold predicate. The body of the predicate may not hold at this point.
  [Error] File "./guarded_witnesses.rav", line 20, columns 49-71:
  20 |     (exists child: Int :: result == child + 1 && own(cell.value, child))
                                                        ^^^^^^^^^^^^^^^^^^^^^^
  Related Location: This own predicate may not hold.
  [Error] File "./guarded_witnesses.rav", line 38, columns 2-27:
  38 |   fold cyclic(cell, false);
         ^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: Failed to fold predicate. The body of the predicate may not hold at this point.
  [Error] File "./guarded_witnesses.rav", line 38, columns 2-27:
  38 |   fold cyclic(cell, false);
         ^^^^^^^^^^^^^^^^^^^^^^^^^
  Related Location: No witness could be computed for $bind_x&1, so it was treated as an arbitrary value.
  [Error] File "./guarded_witnesses.rav", line 38, columns 2-27:
  38 |   fold cyclic(cell, false);
         ^^^^^^^^^^^^^^^^^^^^^^^^^
  Related Location: No witness could be computed for $bind_y&1, so it was treated as an arbitrary value.
  [Error] File "./guarded_witnesses.rav", line 32, columns 4-14:
  32 |     x == y + 1 && y == x + 1 && own(cell.value, 7)
           ^^^^^^^^^^
  Related Location: This assertion may not hold.
  [Error] File "./guarded_witnesses.rav", line 32, columns 18-28:
  32 |     x == y + 1 && y == x + 1 && own(cell.value, 7)
                         ^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]
