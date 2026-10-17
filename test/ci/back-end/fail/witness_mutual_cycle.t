  $ dune exec -- raven --shh ./witness_mutual_cycle.rav
  [Error] File "./witness_mutual_cycle.rav", line 5, columns 9-58:
  5 |   exhale exists a: Int, b: Int :: edge(a, b) && edge(b, a);
               ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: This assertion may not hold: insufficient permissions.
  [Error] File "./witness_mutual_cycle.rav", line 5, columns 16-22:
  5 |   exhale exists a: Int, b: Int :: edge(a, b) && edge(b, a);
                      ^^^^^^
  Related Location: No witness could be computed for a, so it was treated as an arbitrary value.
  [Error] File "./witness_mutual_cycle.rav", line 5, columns 24-30:
  5 |   exhale exists a: Int, b: Int :: edge(a, b) && edge(b, a);
                              ^^^^^^
  Related Location: No witness could be computed for b, so it was treated as an arbitrary value.
  [Error] File "./witness_mutual_cycle.rav", line 5, columns 34-44:
  5 |   exhale exists a: Int, b: Int :: edge(a, b) && edge(b, a);
                                        ^^^^^^^^^^
  Related Location: This predicate may not hold.
  [Error] File "./witness_mutual_cycle.rav", line 5, columns 48-58:
  5 |   exhale exists a: Int, b: Int :: edge(a, b) && edge(b, a);
                                                      ^^^^^^^^^^
  Related Location: This predicate may not hold.
  [1]
