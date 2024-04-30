  $ dune exec -- raven --shh ./masks_1.rav
  [Error] File "./masks_1.rav", line 28, columns 2-10:
  28 |   q(x, v);
         ^^^^^^^^
  Verification Error: Cannot call q. The invariant inv1 required by q is not available in the current mask.
  [1]
