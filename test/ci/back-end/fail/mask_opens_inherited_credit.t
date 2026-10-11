  $ dune exec -- raven --shh ./mask_opens_inherited_credit.rav
  [Error] File "./mask_opens_inherited_credit.rav", line 22, columns 2-22:
  22 |   Renamed.touch(x, y);
         ^^^^^^^^^^^^^^^^^^^^
  Verification Error: Cannot call touch. The invariant pair required by touch is not available in the current mask.
  [1]
