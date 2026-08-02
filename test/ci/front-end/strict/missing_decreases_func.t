  $ dune exec -- raven --shh --strict ./missing_decreases_func.rav
  [Warning] File "./missing_decreases_func.rav", line 1, columns 5-8:
  1 | func fac(n: Int)
           ^^^
  fac is recursive but declares no `decreases` clause; its termination will be assumed for verification purposes, not checked
  Verification successful.
