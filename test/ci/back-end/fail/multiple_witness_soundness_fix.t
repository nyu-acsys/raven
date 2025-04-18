  $ dune exec -- raven --shh multiple_witness_soundness_fix.rav
  [Error] File "multiple_witness_soundness_fix.rav", line 27, columns 4-20:
  27 |     fold is_list(r);
           ^^^^^^^^^^^^^^^^
  Verification Error: Failed to fold predicate. The body of the predicate may not hold at this point.
  [Error] File "multiple_witness_soundness_fix.rav", line 12, columns 19-38:
  12 |         (f1(l) ==> own(n.lock, l, 0.5)) && 
                          ^^^^^^^^^^^^^^^^^^^
  Related Location: This own predicate may not hold.
  [1]
