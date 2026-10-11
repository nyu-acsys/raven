  $ dune exec -- raven --shh ./witness_arithmetic_repeated.rav
  [Warning] File "./witness_arithmetic_repeated.rav", line 5, columns 16-22:
  5 |   exhale exists n: Int :: own(x.f, n + n);
                      ^^^^^^
  No witness could be computed for n -- it will be treated as an arbitrary unconstrained value, which may cause later assertions about it to fail.
  [Error] File "./witness_arithmetic_repeated.rav", line 5, columns 9-41:
  5 |   exhale exists n: Int :: own(x.f, n + n);
               ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: This assertion may not hold: insufficient permissions.
  [Error] File "./witness_arithmetic_repeated.rav", line 5, columns 26-41:
  5 |   exhale exists n: Int :: own(x.f, n + n);
                                ^^^^^^^^^^^^^^^
  Related Location: This own predicate may not hold.
  [1]
