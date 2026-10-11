  $ dune exec -- raven --shh ./witness_equality_guard_cycle.rav
  [Warning] File "./witness_equality_guard_cycle.rav", line 5, columns 16-22:
  5 |   exhale exists n: Int :: (n == 0 ? n == 1 : n == 0) && own(x.f, 7);
                      ^^^^^^
  No witness could be computed for n -- it will be treated as an arbitrary unconstrained value, which may cause later assertions about it to fail.
  [Error] File "./witness_equality_guard_cycle.rav", line 5, columns 9-67:
  5 |   exhale exists n: Int :: (n == 0 ? n == 1 : n == 0) && own(x.f, 7);
               ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: This assertion may not hold: insufficient permissions.
  [Error] File "./witness_equality_guard_cycle.rav", line 5, columns 36-42:
  5 |   exhale exists n: Int :: (n == 0 ? n == 1 : n == 0) && own(x.f, 7);
                                          ^^^^^^
  Related Location: This assertion may not hold.
  [1]
