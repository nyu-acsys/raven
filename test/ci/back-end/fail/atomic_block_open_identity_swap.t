  $ dune exec -- raven --shh ./atomic_block_open_identity_swap.rav
  [Error] File "./atomic_block_open_identity_swap.rav", line 21, column 2 to line 25, column 3:
  21 |   atomic {
         ^^^^^^^^
  Verification Error: An invariant or atomic update opened inside an atomic block must also be closed inside it.
  [1]
