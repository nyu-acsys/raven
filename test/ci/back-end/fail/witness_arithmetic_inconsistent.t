  $ dune exec -- raven --shh ./witness_arithmetic_inconsistent.rav
  [Error] File "./witness_arithmetic_inconsistent.rav", line 5, columns 9-51:
  5 |   exhale exists n: Int :: n + 1 == n && own(x.f, 7);
               ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: This assertion may not hold: insufficient permissions.
  [Error] File "./witness_arithmetic_inconsistent.rav", line 5, columns 16-22:
  5 |   exhale exists n: Int :: n + 1 == n && own(x.f, 7);
                      ^^^^^^
  Related Location: No witness could be computed for n, so it was treated as an arbitrary value.
  [Error] File "./witness_arithmetic_inconsistent.rav", line 5, columns 26-36:
  5 |   exhale exists n: Int :: n + 1 == n && own(x.f, 7);
                                ^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]
