  $ dune exec -- raven --shh ./ghost_result_non_atomic_call.rav
  [Error] File "./ghost_result_non_atomic_call.rav", line 26, columns 2-33:
  26 |   ghost val witness := restore(c)
         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: Cannot take a non-atomic step while an invariant or atomic update is open.
  [Error] File "./ghost_result_non_atomic_call.rav", line 34, columns 2-39:
  34 |   ghost val witness := restore_value(c)
         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: Cannot take a non-atomic step while an invariant or atomic update is open.
  [Error] File "./ghost_result_non_atomic_call.rav", line 44, columns 2-33:
  44 |   ghost val witness := restore(c)
         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: Cannot take a non-atomic step while an invariant or atomic update is open.
  [1]
