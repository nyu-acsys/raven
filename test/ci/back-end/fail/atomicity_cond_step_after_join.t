  $ dune exec -- raven --shh ./atomicity_cond_step_after_join.rav
  [Error] File "./atomicity_cond_step_after_join.rav", line 16, columns 2-12:
  16 |   c.fa := 2;
         ^^^^^^^^^^
  Verification Error: Attempting to take more than one atomic step with an open invariant or atomic update.
  [1]
