  $ dune exec -- raven --shh ./exact_call.rav
  [Error] File "./exact_call.rav", line 13, columns 2-15:
  13 |   root_step(x);
         ^^^^^^^^^^^^^
  Verification Error: Cannot call root_step. The invariant root required by root_step is not available in the current mask.
  [1]
