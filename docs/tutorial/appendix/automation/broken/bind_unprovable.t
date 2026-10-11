  $ dune exec -- raven --shh ./bind_unprovable.rav
  [Error] File "./bind_unprovable.rav", line 22, columns 10-41:
  22 |   x, y :| x + y == 10 && x >= 0 && y >= 0
                 ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: The right-hand side of this bind statement may not hold.
  [1]
