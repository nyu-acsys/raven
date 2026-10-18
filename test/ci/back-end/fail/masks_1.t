  $ dune exec -- raven --shh ./masks_1.rav
  [Error] File "./masks_1.rav", line 28, columns 2-10:
  28 |   q(x, v);
         ^^^^^^^^
  Verification Error: Missing fold for unfolded invariant inv1(x, v).
  [Error] File "./masks_1.rav", line 27, columns 2-19:
  27 |   unfold inv1(x,v);
         ^^^^^^^^^^^^^^^^^
  Related Location: inv1(x, v) was unfolded here.
  [1]
