  $ dune exec -- raven --shh --strict ./loop_in_lemma_no_decreases.rav
  [Warning] File "./loop_in_lemma_no_decreases.rav", line 6, column 4 to line 10, column 5:
  6 |     while (i > 0)
          ^^^^^^^^^^^^^
  countdown_loop is recursive but declares no `decreases` clause; its termination will be assumed for verification purposes, not checked
  Verification successful.
