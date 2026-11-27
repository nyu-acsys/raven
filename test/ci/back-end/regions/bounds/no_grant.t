  $ dune exec -- raven --shh ./no_grant.rav
  [Error] File "./no_grant.rav", line 31, columns 2-11:
  31 |   touch(x);
         ^^^^^^^^^
  Verification Error: Cannot call touch. The invariant cell required by touch is not available in the current mask.
  [1]
