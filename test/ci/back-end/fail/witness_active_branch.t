  $ dune exec -- raven --shh ./witness_active_branch.rav
  [Error] File "./witness_active_branch.rav", line 8, columns 9-52:
  8 |   exhale idle(7) is idle ? own(x.f, 8) : own(x.f, 7);
               ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: This assertion may not hold: insufficient permissions.
  [Error] File "./witness_active_branch.rav", line 8, columns 27-38:
  8 |   exhale idle(7) is idle ? own(x.f, 8) : own(x.f, 7);
                                 ^^^^^^^^^^^
  Related Location: This own predicate may not hold.
  [1]
