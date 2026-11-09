  $ raven --shh au_snapshot_block.rav
  [Error] File "au_snapshot_block.rav", line 7, column 2 to line 12, column 3:
  7 |   atomic {
        ^^^^^^^^
  Verification Error: An invariant or atomic update opened inside an atomic block must also be closed inside it.
  [1]
