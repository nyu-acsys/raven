  $ dune exec -- raven --shh ./invariant_alloc_fail.rav
  [Error] File "./invariant_alloc_fail.rav", line 12, columns 2-21:
  12 |   fold counterInv(x);
         ^^^^^^^^^^^^^^^^^^^
  Error: Invariant not already opened; cannot be closed. Invariant not in mask; cannot be allocated..
  [1]
