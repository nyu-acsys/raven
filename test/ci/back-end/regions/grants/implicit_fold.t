  $ dune exec -- raven --shh ./implicit_fold.rav
  [Error] File "./implicit_fold.rav", line 13, columns 2-19:
  13 |   need(owner, key);
         ^^^^^^^^^^^^^^^^^
  Verification Error: Cannot call need. The invariant item required by need is not available in the current mask.
  [1]
