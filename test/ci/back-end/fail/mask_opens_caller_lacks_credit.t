  $ dune exec -- raven --shh ./mask_opens_caller_lacks_credit.rav
  [Error] File "./mask_opens_caller_lacks_credit.rav", line 22, columns 2-10:
  22 |   peek(y);
         ^^^^^^^^
  Verification Error: Cannot call peek. The invariant cell required by peek is not available in the current mask.
  [1]
