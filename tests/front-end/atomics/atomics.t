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
  Error: Invariant already opened
  [1]

  $ dune exec -- ../../../bin/raven.exe --shh ./fail/fail1.rav
  [Error] File "./fail/fail1.rav", line 8, column 0 to line 23, column 1:
  8 | {
      ^
  Verification Error: Could not prove that atomic update has been committed.
  [1]

  $ dune exec -- ../../../bin/raven.exe --shh ./fail/fail2.rav
  [Error] File "./fail/fail2.rav", line 22, columns 2-14:
  22 |   return x1+2;
         ^^^^^^^^^^^^
  Verification Error: Could not prove atomic postcondition at return stmt.
  [1]
