  $ dune exec -- raven --shh ./witness_unknown_guard.rav
  [Warning] File "./witness_unknown_guard.rav", line 8, columns 29-39:
  8 |   exhale condition ? (exists token: Int :: ticket(token)) : own(x.f, 7);
                                   ^^^^^^^^^^
  No witness could be computed for token -- it will be treated as an arbitrary unconstrained value, which may cause later assertions about it to fail.
  [Error] File "./witness_unknown_guard.rav", line 8, columns 9-71:
  8 |   exhale condition ? (exists token: Int :: ticket(token)) : own(x.f, 7);
               ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: This assertion may not hold: insufficient permissions.
  [Error] File "./witness_unknown_guard.rav", line 8, columns 43-56:
  8 |   exhale condition ? (exists token: Int :: ticket(token)) : own(x.f, 7);
                                                 ^^^^^^^^^^^^^
  Related Location: This predicate may not hold.
  [1]
