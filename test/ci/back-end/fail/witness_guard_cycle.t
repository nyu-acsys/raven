  $ dune exec -- raven --shh ./witness_guard_cycle.rav
  [Warning] File "./witness_guard_cycle.rav", line 5, columns 16-22:
  5 |   exhale exists n: Int :: n == 0 ? edge(0, n) : edge(1, n);
                      ^^^^^^
  No witness could be computed for n -- it will be treated as an arbitrary unconstrained value, which may cause later assertions about it to fail.
  [Error] File "./witness_guard_cycle.rav", line 5, columns 9-58:
  5 |   exhale exists n: Int :: n == 0 ? edge(0, n) : edge(1, n);
               ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: This assertion may not hold: insufficient permissions.
  [Error] File "./witness_guard_cycle.rav", line 5, columns 35-45:
  5 |   exhale exists n: Int :: n == 0 ? edge(0, n) : edge(1, n);
                                         ^^^^^^^^^^
  Related Location: This predicate may not hold.
  [1]
