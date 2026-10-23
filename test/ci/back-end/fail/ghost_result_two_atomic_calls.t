  $ dune exec -- raven --shh ./ghost_result_two_atomic_calls.rav
  [Error] File "./ghost_result_two_atomic_calls.rav", line 30, columns 2-32:
  30 |   ghost val second := logical(c)
         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: Attempting to take more than one atomic step with an open invariant or atomic update.
  [Error] File "./ghost_result_two_atomic_calls.rav", line 39, columns 2-33:
  39 |   ghost val second := physical(c)
         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: Attempting to take more than one atomic step with an open invariant or atomic update.
  [1]
