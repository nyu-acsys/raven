  $ dune exec -- raven --shh ./mask_opens_grant_restricted.rav
  [Error] File "./mask_opens_grant_restricted.rav", line 27, columns 2-17:
  27 |   unfold cell(x);
         ^^^^^^^^^^^^^^^
  Verification Error: Invariant cell is not in the current mask.
  [1]
