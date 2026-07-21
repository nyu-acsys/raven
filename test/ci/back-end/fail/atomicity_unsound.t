  $ dune exec -- raven --shh ./atomicity_unsound.rav
  [Error] File "./atomicity_unsound.rav", line 15, columns 2-15:
  15 |   fold test(x);
         ^^^^^^^^^^^^^
  Verification Error: Cannot fold test: its arguments no longer match the instance that was opened by the corresponding unfold (a variable used to identify the instance may have been reassigned in between).
  [1]
