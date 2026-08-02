  $ dune exec -- raven --shh --strict ./free_user.rav
  [Warning] File "./free_user.rav", line 1, columns 10-13:
  1 | free proc foo()
                ^^^
  procedure foo is declared `free`; its contract will be assumed for verification purposes, not checked
  Verification successful.
