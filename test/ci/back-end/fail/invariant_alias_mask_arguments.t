  $ dune exec -- raven --shh ./invariant_alias_mask_arguments.rav
  [Error] File "./invariant_alias_mask_arguments.rav", line 25, columns 2-19:
  25 | { Applied.touch(y); }
         ^^^^^^^^^^^^^^^^^
  Verification Error: Cannot call touch. The invariant shared required by touch is not available in the current mask.
  [1]
