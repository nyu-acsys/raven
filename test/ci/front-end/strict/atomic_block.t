  $ dune exec -- raven --shh --strict ./atomic_block.rav
  [Warning] File "./atomic_block.rav", line 13, column 2 to line 16, column 3:
  13 |   atomic {
         ^^^^^^^^
  this `atomic` block's body is assumed to be a single machine step, not checked; Raven has no model of the target machine to verify that against
  [Warning] File "./atomic_block.rav", line 24, column 2 to line 28, column 3:
  24 |   atomic {
         ^^^^^^^^
  this `atomic` block's body is assumed to be a single machine step, not checked; Raven has no model of the target machine to verify that against
  Verification successful.
