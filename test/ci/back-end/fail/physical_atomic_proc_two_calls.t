  $ dune exec -- raven --shh ./physical_atomic_proc_two_calls.rav
  [Error] File "./physical_atomic_proc_two_calls.rav", line 17, columns 2-12:
  17 |   restore(c)
         ^^^^^^^^^^
  Verification Error: Attempting to take more than one atomic step with an open invariant or atomic update.
  [1]
