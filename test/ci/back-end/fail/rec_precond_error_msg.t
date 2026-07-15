  $ dune exec -- raven --shh ./rec_precond_error_msg.rav
  [Error] File "./rec_precond_error_msg.rav", line 11, columns 2-17:
  11 |   rec_bad(n - 1);
         ^^^^^^^^^^^^^^^
  Verification Error: A precondition may not hold for this call.
  [Error] File "./rec_precond_error_msg.rav", line 8, columns 11-17:
  8 |   requires n >= 0
                 ^^^^^^
  Related Location: This assertion may not hold.
  [1]
