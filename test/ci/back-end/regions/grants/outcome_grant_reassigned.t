  $ dune exec -- raven --shh ./outcome_grant_reassigned.rav
  [Error] File "./outcome_grant_reassigned.rav", line 34, columns 2-11:
  34 |   touch(q);
         ^^^^^^^^^
  Verification Error: Cannot call touch. The invariant shared required by touch is not available in the current mask.
  [1]
