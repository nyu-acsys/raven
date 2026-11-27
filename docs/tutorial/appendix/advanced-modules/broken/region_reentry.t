  $ dune exec -- raven --shh ./region_reentry.rav
  [Error] File "./region_reentry.rav", line 20, columns 2-15:
  20 |   root_step(x);
         ^^^^^^^^^^^^^
  Verification Error: Missing fold for unfolded invariant child(x).
  [Error] File "./region_reentry.rav", line 19, columns 2-18:
  19 |   unfold child(x);
         ^^^^^^^^^^^^^^^^
  Related Location: child(x) was unfolded here.
  [1]
