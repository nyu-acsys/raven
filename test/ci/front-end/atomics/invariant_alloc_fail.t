  $ dune exec -- raven --shh ./invariant_alloc_fail.rav
  [Error] File "./invariant_alloc_fail.rav", line 12, columns 2-21:
  12 |   fold counterInv(x);
         ^^^^^^^^^^^^^^^^^^^
  Error: Cannot close invariant counterInv: it is neither currently open nor available in the mask to be freshly allocated.
  [1]
