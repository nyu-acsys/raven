  $ dune exec -- raven --shh ./atomicity_atomic_op_two_steps.rav
  [Error] File "./atomicity_atomic_op_two_steps.rav", line 18, columns 2-24:
  18 |   val y := faa(c.fb, 1);
         ^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: Attempting to take more than one atomic step with an open invariant or atomic update.
  [1]
