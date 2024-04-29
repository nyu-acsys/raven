  $ dune exec -- raven --shh ./fpu_fail.rav
  [Error] File "./fpu_fail.rav", line 7, columns 2-15:
  7 |   fpu(x, f, 4);
        ^^^^^^^^^^^^^
  Verification Error: This update may not be frame-preserving.
  [1]
