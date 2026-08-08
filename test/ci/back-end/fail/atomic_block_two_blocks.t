  $ dune exec -- raven --shh ./atomic_block_two_blocks.rav
  [Error] File "./atomic_block_two_blocks.rav", line 14, column 2 to line 16, column 3:
  14 |   atomic {
         ^^^^^^^^
  Verification Error: Attempting to take more than one atomic step with an open invariant or atomic update.
  [1]
