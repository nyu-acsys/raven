  $ dune exec -- raven --shh ./witness_fallback_fail.rav
  [Error] File "./witness_fallback_fail.rav", line 16, columns 2-18:
  16 |   fold bounded(x);
         ^^^^^^^^^^^^^^^^
  Verification Error: Failed to fold predicate. The body of the predicate may not hold at this point.
  [Error] File "./witness_fallback_fail.rav", line 16, columns 2-18:
  16 |   fold bounded(x);
         ^^^^^^^^^^^^^^^^
  Related Location: No witness could be computed for k, so the value from the unfold at line 13 was used.
  [Error] File "./witness_fallback_fail.rav", line 6, columns 42-48:
  6 |   exists v: Int, k: Int :: own(x.f, v) && v <= k
                                                ^^^^^^
  Related Location: This assertion may not hold.
  [Error] File "./witness_fallback_fail.rav", line 29, columns 2-18:
  29 |   fold bounded(z);
         ^^^^^^^^^^^^^^^^
  Verification Error: Failed to fold predicate. The body of the predicate may not hold at this point.
  [Error] File "./witness_fallback_fail.rav", line 6, columns 17-23:
  6 |   exists v: Int, k: Int :: own(x.f, v) && v <= k
                       ^^^^^^
  Related Location: No witness could be computed for k, so it was treated as an arbitrary value.
  [Error] File "./witness_fallback_fail.rav", line 6, columns 42-48:
  6 |   exists v: Int, k: Int :: own(x.f, v) && v <= k
                                                ^^^^^^
  Related Location: This assertion may not hold.
  [Error] File "./witness_fallback_fail.rav", line 31, columns 2-18:
  31 |   fold bounded(z);
         ^^^^^^^^^^^^^^^^
  Verification Error: Failed to fold predicate. The body of the predicate may not hold at this point.
  [Error] File "./witness_fallback_fail.rav", line 6, columns 17-23:
  6 |   exists v: Int, k: Int :: own(x.f, v) && v <= k
                       ^^^^^^
  Related Location: No witness could be computed for k, so it was treated as an arbitrary value.
  [Error] File "./witness_fallback_fail.rav", line 6, columns 42-48:
  6 |   exists v: Int, k: Int :: own(x.f, v) && v <= k
                                                ^^^^^^
  Related Location: This assertion may not hold.
  [1]
