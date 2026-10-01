  $ dune exec -- raven --shh ./atomicity_cond_snapshot_drift.rav
  [Error] File "./atomicity_cond_snapshot_drift.rav", line 22, columns 2-16:
  22 |   fold a_inv(u);
         ^^^^^^^^^^^^^^
  Verification Error: Cannot fold a_inv: its arguments no longer match the instance that was opened by the corresponding unfold (a variable used to identify the instance may have been reassigned in between).
  [1]
