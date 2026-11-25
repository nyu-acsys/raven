  $ dune exec -- raven --shh ./ancestor_call.rav
  [Error] File "./ancestor_call.rav", line 16, columns 2-15:
  16 |   root_step(x);
         ^^^^^^^^^^^^^
  Verification Error: Missing fold for unfolded invariant child(x, 0).
  [Error] File "./ancestor_call.rav", line 15, columns 2-21:
  15 |   unfold child(x, 0);
         ^^^^^^^^^^^^^^^^^^^
  Related Location: child(x, 0) was unfolded here.
  [1]
