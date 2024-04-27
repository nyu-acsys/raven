Atomic Commands Test

  $ dune exec -- ../../../bin/raven.exe --shh ./test1.rav
  Verification successful.

  $ dune exec -- ../../../bin/raven.exe --shh ./test2.rav
  Verification successful.


  $ dune exec -- ../../../bin/raven.exe --shh ./test3.rav
  Verification successful.

  $ dune exec -- ../../../bin/raven.exe --shh ./test4.rav
  [Error] File "./test4.rav", line 14, columns 2-17:
  14 |   unfold p2(1+1);
         ^^^^^^^^^^^^^^^
  Verification Error: Cannot open invariant p2. Invariant already opened or not in mask.
  [1]

  $ dune exec -- ../../../bin/raven.exe --shh ./fail/fail1.rav
  [Error] File "./fail/fail1.rav", line 23, columns 1-1:
  23 | }
        ^
  Verification Error: The atomic specification may not have been committed before reaching this return point.
  [1]

  $ dune exec -- ../../../bin/raven.exe --shh ./fail/fail2.rav
  [Error] File "./fail/fail2.rav", line 22, columns 2-14:
  22 |   return x1+2;
         ^^^^^^^^^^^^
  Verification Error: The atomic specification may not have been committed before reaching this return point.
  [1]
