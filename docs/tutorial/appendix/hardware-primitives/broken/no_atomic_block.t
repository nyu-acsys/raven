  $ dune exec -- raven --shh ./no_atomic_block.rav
  [Error] File "./no_atomic_block.rav", line 26, columns 2-15:
  26 |   c.right := 1;
         ^^^^^^^^^^^^^
  Verification Error: Attempting to take more than one atomic step with an open invariant or atomic update.
  [1]
