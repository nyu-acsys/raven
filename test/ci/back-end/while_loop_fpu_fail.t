  $ dune exec -- raven --shh ./while_loop_fpu_fail.rav
  [Error] File "./while_loop_fpu_fail.rav", line 8, columns 14-53:
  8 |     invariant own(x, plink, Fink.frac_chunk(10, 1.0)) 
                    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: This loop invariant may not be maintained.
  [Error] File "./while_loop_fpu_fail.rav", line 8, columns 14-53:
  8 |     invariant own(x, plink, Fink.frac_chunk(10, 1.0)) 
                    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: This loop invariant may not be maintained.
  [Error] File "./while_loop_fpu_fail.rav", line 8, columns 14-53:
  8 |     invariant own(x, plink, Fink.frac_chunk(10, 1.0)) 
                    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Related Location: This own predicate may not hold.
  [1]
