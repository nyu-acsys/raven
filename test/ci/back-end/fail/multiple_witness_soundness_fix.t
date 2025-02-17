  $ dune exec -- raven --shh multiple_witness_soundness_fix.rav
  [Error] File "multiple_witness_soundness_fix.rav", line 26, columns 4-20:
  26 |     fold is_list(r);
           ^^^^^^^^^^^^^^^^
  Verification Error: Failed to fold predicate. The body of the predicate may not hold at this point.
  [1]
