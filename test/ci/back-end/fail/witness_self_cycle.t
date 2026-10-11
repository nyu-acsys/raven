  $ dune exec -- raven --shh ./witness_self_cycle.rav
  [Warning] File "./witness_self_cycle.rav", line 5, columns 16-22:
  5 |   exhale exists i: Int :: edge(i, i);
                      ^^^^^^
  No witness could be computed for i -- it will be treated as an arbitrary unconstrained value, which may cause later assertions about it to fail.
  [Error] File "./witness_self_cycle.rav", line 5, columns 9-36:
  5 |   exhale exists i: Int :: edge(i, i);
               ^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: This assertion may not hold: insufficient permissions.
  [Error] File "./witness_self_cycle.rav", line 5, columns 26-36:
  5 |   exhale exists i: Int :: edge(i, i);
                                ^^^^^^^^^^
  Related Location: This predicate may not hold.
  [1]
