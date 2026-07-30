  $ dune exec -- raven --shh --strict ./free_via_include.rav
  [Warning] File "free_included_lib.rav", line 1, columns 10-13:
  1 | free proc bar()
                ^^^
  procedure bar is declared `free`; its contract will be assumed for verification purposes, not checked
  Verification successful.
