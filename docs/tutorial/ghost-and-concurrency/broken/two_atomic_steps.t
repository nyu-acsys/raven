  $ dune exec -- raven --shh ./two_atomic_steps.rav
  [Error] File "./two_atomic_steps.rav", line 27, columns 2-18:
  27 |   c.count := x + 1
         ^^^^^^^^^^^^^^^^
  Verification Error: Attempting to take more than one atomic step with an open invariant or atomic update.
  [1]
