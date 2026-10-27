  $ dune exec -- raven --shh ./invariant_alias_masks.rav
  [Error] File "./invariant_alias_masks.rav", line 43, columns 2-19:
  43 |   Applied.touch(x);
         ^^^^^^^^^^^^^^^^^
  Verification Error: Cannot call touch. The invariant shared required by touch is not available in the current mask.
  [1]
