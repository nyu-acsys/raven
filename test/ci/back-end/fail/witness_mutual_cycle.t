  $ dune exec -- raven --shh ./witness_mutual_cycle.rav
  [Warning] File "./witness_mutual_cycle.rav", line 5, columns 16-22:
  5 |   exhale exists a: Int, b: Int :: edge(a, b) && edge(b, a);
                      ^^^^^^
  No witness could be computed for a -- it will be treated as an arbitrary unconstrained value, which may cause later assertions about it to fail.
  [Warning] File "./witness_mutual_cycle.rav", line 5, columns 24-30:
  5 |   exhale exists a: Int, b: Int :: edge(a, b) && edge(b, a);
                              ^^^^^^
  No witness could be computed for b -- it will be treated as an arbitrary unconstrained value, which may cause later assertions about it to fail.
  [Error] File "./witness_mutual_cycle.rav", line 5, columns 9-58:
  5 |   exhale exists a: Int, b: Int :: edge(a, b) && edge(b, a);
               ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: This assertion may not hold: insufficient permissions.
  [Error] File "./witness_mutual_cycle.rav", line 5, columns 34-44:
  5 |   exhale exists a: Int, b: Int :: edge(a, b) && edge(b, a);
                                        ^^^^^^^^^^
  Related Location: This predicate may not hold.
  [1]
