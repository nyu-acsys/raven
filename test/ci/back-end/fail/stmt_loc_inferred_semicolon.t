  $ dune exec -- raven --shh ./stmt_loc_inferred_semicolon.rav
  [Error] File "./stmt_loc_inferred_semicolon.rav", line 21, columns 2-14:
  21 |   val b := x.f
         ^^^^^^^^^^^^
  Verification Error: Attempting to take more than one atomic step with an open invariant or atomic update.
  [1]
