  $ dune exec -- raven --shh ./duplicate.rav
  [Error] File "./duplicate.rav", line 9, columns 2-21:
  9 |   unfold child(x, 0);
        ^^^^^^^^^^^^^^^^^^^
  Verification Error: Invariant child is already open.
  [1]
