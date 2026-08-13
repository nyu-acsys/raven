  $ dune exec -- raven --shh ./frac_witness_fallback_insufficient.rav
  [Error] File "./frac_witness_fallback_insufficient.rav", line 14, columns 2-25:
  14 |   val b := cas(x.f, 1, 2)
         ^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: A precondition may not hold for this call.
  [Error] File "lib/library/atomics.rav", line 55, columns 56-64:
  55 |     atomic requires own(x.A.f, v, q) && (v == old_val ? q == 1.0 : q > 0)
                                                               ^^^^^^^^
  Related Location: This assertion may not hold.
  [1]
