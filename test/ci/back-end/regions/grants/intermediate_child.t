  $ dune exec -- raven --shh ./intermediate_child.rav
  [Error] File "./intermediate_child.rav", line 16, columns 2-18:
  16 |   unfold child(x);
         ^^^^^^^^^^^^^^^^
  Verification Error: Invariant child is not in the current mask.
  [1]
