  $ dune exec -- ../../../bin/raven.exe --shh ./fpu_fail.rav
  [Error] File "./fpu_fail.rav", line 7, columns 2-15:
  7 |   fpu(x, f, 4);
        ^^^^^^^^^^^^^
  Verification Error: Could not prove validity of fpu.
  [1]
