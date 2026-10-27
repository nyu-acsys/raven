  $ dune exec -- raven --shh ./namespace_layout_argument_distinct.rav
  [Error] File "./namespace_layout_argument_distinct.rav", line 50, columns 2-22:
  50 | { Applied.touch(item); }
         ^^^^^^^^^^^^^^^^^^^^
  Verification Error: Cannot call touch. The invariant shared required by touch is not available in the current mask.
  [1]
