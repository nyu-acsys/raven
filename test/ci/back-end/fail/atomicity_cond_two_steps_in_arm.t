  $ dune exec -- raven --shh ./atomicity_cond_two_steps_in_arm.rav
  [Error] File "./atomicity_cond_two_steps_in_arm.rav", line 15, columns 22-32:
  15 |   if (k) { c.fa := 1; c.fb := 2; } else { c.fb := 1; }
                             ^^^^^^^^^^
  Verification Error: Attempting to take more than one atomic step with an open invariant or atomic update.
  [1]
