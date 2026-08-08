  $ dune exec -- raven --shh ./atomic_block_unbalanced.rav
  [Error] File "./atomic_block_unbalanced.rav", line 11, column 2 to line 14, column 3:
  11 |   atomic {
         ^^^^^^^^
  Verification Error: An invariant or atomic update opened inside an atomic block must also be closed inside it.
  [1]
