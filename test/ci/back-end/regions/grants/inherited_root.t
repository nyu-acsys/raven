  $ dune exec -- raven --shh ./inherited_root.rav
  [Error] File "./inherited_root.rav", line 8, columns 2-18:
  8 |   unfold child(x);
        ^^^^^^^^^^^^^^^^
  Verification Error: Invariant child is not in the current mask.
  [1]
