  $ dune exec -- raven --shh bind_4.rav
  [Error] File "bind_4.rav", line 7, columns 7-23:
  7 |   v :| own(x.f, v, 1.0);
             ^^^^^^^^^^^^^^^^
  Verification Error: The right-hand side of this bind statement may not hold.
  [1]
