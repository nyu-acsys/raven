  $ dune exec -- raven --shh ./withheld_allocation.rav
  [Error] File "./withheld_allocation.rav", line 8, columns 2-18:
  8 |   unfold child(x);
        ^^^^^^^^^^^^^^^^
  Verification Error: Invariant child is not in the current mask.
  [1]
