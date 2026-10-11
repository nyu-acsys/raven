  $ dune exec -- raven --shh ./witness_arithmetic_inconsistent.rav
  [Warning] File "./witness_arithmetic_inconsistent.rav", line 5, columns 16-22:
  5 |   exhale exists n: Int :: n + 1 == n && own(x.f, 7);
                      ^^^^^^
  No witness could be computed for n -- it will be treated as an arbitrary unconstrained value, which may cause later assertions about it to fail.
  [Error] File "./witness_arithmetic_inconsistent.rav", line 5, columns 9-51:
  5 |   exhale exists n: Int :: n + 1 == n && own(x.f, 7);
               ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: This assertion may not hold: insufficient permissions.
  [Error] File "./witness_arithmetic_inconsistent.rav", line 5, columns 26-36:
  5 |   exhale exists n: Int :: n + 1 == n && own(x.f, 7);
                                ^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]
