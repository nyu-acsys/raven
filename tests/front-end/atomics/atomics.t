Atomic Commands Test

  $ dune exec -- ../../../bin/raven.exe --shh ./test1.rav
  Verification successful.

  $ dune exec -- ../../../bin/raven.exe --shh ./test2.rav
  Verification successful.


  $ dune exec -- ../../../bin/raven.exe --shh ./test3.rav
  Verification successful.

  $ dune exec -- ../../../bin/raven.exe --shh ./test4.rav
  Verification successful.

  $ dune exec -- ../../../bin/raven.exe --shh ./fail/fail1.rav
  [Error] File "./fail/fail1.rav", line 8, column 0 to line 23, column 1:
  8 | {
      ^
  SMT Error: Assertion is not valid
  [1]

  $ dune exec -- ../../../bin/raven.exe --shh ./fail/fail2.rav
  [Error] File "./fail/fail2.rav", line 22, columns 2-14:
  22 |   return x1+2;
         ^^^^^^^^^^^^
  SMT Error: Assertion is not valid
  [1]
