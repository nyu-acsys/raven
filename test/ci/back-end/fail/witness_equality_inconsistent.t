  $ dune exec -- raven --shh ./witness_equality_inconsistent.rav
  [Error] File "./witness_equality_inconsistent.rav", line 5, columns 9-57:
  5 |   exhale exists n: Int :: n == 1 && n == 2 && own(x.f, 7);
               ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: This assertion may not hold: insufficient permissions.
  [Error] File "./witness_equality_inconsistent.rav", line 5, columns 26-32:
  5 |   exhale exists n: Int :: n == 1 && n == 2 && own(x.f, 7);
                                ^^^^^^
  Related Location: This assertion may not hold.
  [Error] File "./witness_equality_inconsistent.rav", line 5, columns 36-42:
  5 |   exhale exists n: Int :: n == 1 && n == 2 && own(x.f, 7);
                                          ^^^^^^
  Related Location: This assertion may not hold.
  [1]
