  $ dune exec -- raven --shh ./mask_call_longer_candidate.rav
  [Error] File "./mask_call_longer_candidate.rav", line 32, columns 2-15:
  32 |   use_outer(x);
         ^^^^^^^^^^^^^
  Verification Error: Cannot call use_outer. The invariant inner required by use_outer is not available in the current mask.
  [1]
