  $ dune exec -- raven --shh ./witness_arithmetic_conflicting.rav
  [Error] File "./witness_arithmetic_conflicting.rav", line 5, columns 9-61:
  5 |   exhale exists n: Int :: n + 1 == 3 && n == 4 && own(x.f, 7);
               ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: This assertion may not hold: insufficient permissions.
  [Error] File "./witness_arithmetic_conflicting.rav", line 5, columns 26-36:
  5 |   exhale exists n: Int :: n + 1 == 3 && n == 4 && own(x.f, 7);
                                ^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]
