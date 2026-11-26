  $ dune exec -- raven --shh ./returned_input_fail.rav
  [Error] File "./returned_input_fail.rav", line 40, columns 2-10:
  40 |   I.m(41);
         ^^^^^^^^
  Verification Error: Cannot call m. The invariant v required by m is not available in the current mask.
  [1]
