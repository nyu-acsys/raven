  $ dune exec -- raven --shh ./witness_arithmetic_repeated.rav
  [Error] File "./witness_arithmetic_repeated.rav", line 5, columns 9-41:
  5 |   exhale exists n: Int :: own(x.f, n + n);
               ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: This assertion may not hold: insufficient permissions.
  [Error] File "./witness_arithmetic_repeated.rav", line 5, columns 16-22:
  5 |   exhale exists n: Int :: own(x.f, n + n);
                      ^^^^^^
  Related Location: No witness could be computed for n, so it was treated as an arbitrary value.
  [Error] File "./witness_arithmetic_repeated.rav", line 5, columns 26-41:
  5 |   exhale exists n: Int :: own(x.f, n + n);
                                ^^^^^^^^^^^^^^^
  Related Location: This own predicate may not hold.
  [1]
