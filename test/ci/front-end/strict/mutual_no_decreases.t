  $ dune exec -- raven --shh --strict ./mutual_no_decreases.rav
  [Warning] File "./mutual_no_decreases.rav", line 1, columns 5-13:
  1 | func bad_even(n: Int) returns (res: Bool)
           ^^^^^^^^
  bad_even is recursive but declares no `decreases` clause; its termination will be assumed for verification purposes, not checked
  [Warning] File "./mutual_no_decreases.rav", line 6, columns 5-12:
  6 | func bad_odd(n: Int) returns (res: Bool)
           ^^^^^^^
  bad_odd is recursive but declares no `decreases` clause; its termination will be assumed for verification purposes, not checked
  Verification successful.
