  $ dune exec -- raven --shh ./array_index_atomic_steps.rav
  [Error] File "./array_index_atomic_steps.rav", line 14, columns 2-12:
  14 |   y := a[1];
         ^^^^^^^^^^
  Verification Error: Attempting to take more than one atomic step with an open invariant or atomic update.
  [1]
