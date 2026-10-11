  $ dune exec -- raven --shh ./witness_arithmetic_mixed_types.rav
  [Warning] File "./witness_arithmetic_mixed_types.rav", line 5, columns 16-22:
  5 |   exhale exists n: Int :: own(x.f, 1.0 + n);
                      ^^^^^^
  No witness could be computed for n -- it will be treated as an arbitrary unconstrained value, which may cause later assertions about it to fail.
  [Error] File "./witness_arithmetic_mixed_types.rav", line 5, columns 9-43:
  5 |   exhale exists n: Int :: own(x.f, 1.0 + n);
               ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: This assertion may not hold: insufficient permissions.
  [Error] File "./witness_arithmetic_mixed_types.rav", line 5, columns 26-43:
  5 |   exhale exists n: Int :: own(x.f, 1.0 + n);
                                ^^^^^^^^^^^^^^^^^
  Related Location: This own predicate may not hold.
  [1]
