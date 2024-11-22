  $ dune exec -- raven --shh bind_2.rav
  [Error] File "bind_2.rav", line 3, columns 7-22:
  3 |   x :| x < 7 && 10 < x;
             ^^^^^^^^^^^^^^^
  Verification Error: The right-hand side of this bind statement may not hold.
  [1]
