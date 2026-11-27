  $ dune exec -- raven --shh ./exact_allocation.rav
  [Error] File "./exact_allocation.rav", line 9, columns 2-21:
  9 |   unfold child(x, 0);
        ^^^^^^^^^^^^^^^^^^^
  Verification Error: Invariant child is not in the current mask.
  [1]
