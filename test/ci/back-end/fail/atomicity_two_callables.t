The atomicity errors of every callable are reported, not just the first:

  $ dune exec -- raven --shh ./atomicity_two_callables.rav
  [Error] File "./atomicity_two_callables.rav", line 17, columns 2-24:
  17 |   val y := faa(c.fb, 1);
         ^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: Attempting to take more than one atomic step with an open invariant or atomic update.
  [Error] File "./atomicity_two_callables.rav", line 26, columns 2-24:
  26 |   val y := faa(c.fa, 1);
         ^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: Attempting to take more than one atomic step with an open invariant or atomic update.
  [1]
