  $ dune exec -- raven --shh ./atomic_block_reopen_step.rav
  [Error] File "./atomic_block_reopen_step.rav", line 22, columns 2-10:
  22 |   x.f := 2
         ^^^^^^^^
  Verification Error: Attempting to take more than one atomic step with an open invariant or atomic update.
  [1]
