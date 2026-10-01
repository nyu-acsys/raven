  $ dune exec -- raven --shh ./mask_opens_body_outside.rav
  [Error] File "./mask_opens_body_outside.rav", line 13, columns 2-17:
  13 |   unfold cell(x);
         ^^^^^^^^^^^^^^^
  Verification Error: Invariant cell is not in the current mask.
  [1]
