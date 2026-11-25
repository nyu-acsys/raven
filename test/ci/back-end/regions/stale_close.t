  $ dune exec -- raven --shh ./stale_close.rav
  [Error] File "./stale_close.rav", line 11, columns 2-21:
  11 |   unfold child(x, 0);
         ^^^^^^^^^^^^^^^^^^^
  Verification Error: Invariant child is not in the current mask.
  [1]
