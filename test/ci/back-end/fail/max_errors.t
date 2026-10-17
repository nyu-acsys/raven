Every failed assertion is reported:

  $ dune exec -- raven --shh ./max_errors.rav
  [Error] File "./max_errors.rav", line 3, columns 9-14:
  3 |   assert x > 0;
               ^^^^^
  Verification Error: This assertion may be violated.
  [Error] File "./max_errors.rav", line 4, columns 9-14:
  4 |   assert x > 1;
               ^^^^^
  Verification Error: This assertion may be violated.
  [Error] File "./max_errors.rav", line 8, columns 9-14:
  8 |   assert x > 2;
               ^^^^^
  Verification Error: This assertion may be violated.
  [1]

With --max-errors, checking stops once there are more errors than the limit:

  $ dune exec -- raven --shh --max-errors=2 ./max_errors.rav
  [Error] File "./max_errors.rav", line 3, columns 9-14:
  3 |   assert x > 0;
               ^^^^^
  Verification Error: This assertion may be violated.
  [Error] File "./max_errors.rav", line 4, columns 9-14:
  4 |   assert x > 1;
               ^^^^^
  Verification Error: This assertion may be violated.
  [Error] Error: Stopped after 2 errors; use --max-errors to change the limit
  [1]
