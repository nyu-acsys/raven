  $ dune exec -- raven --shh ./invariant_alias_mask_fresh.rav
  [Error] File "./invariant_alias_mask_fresh.rav", line 24, columns 2-19:
  24 | { Applied.touch(x); }
         ^^^^^^^^^^^^^^^^^
  Verification Error: Cannot call touch. The invariant shared required by touch is not available in the current mask.
  [1]
