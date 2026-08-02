  $ dune exec -- raven --shh --strict ./missing_decreases_lemma.rav
  [Warning] File "./missing_decreases_lemma.rav", line 1, columns 6-18:
  1 | lemma sum_contract(n: Int)
            ^^^^^^^^^^^^
  sum_contract is recursive but declares no `decreases` clause; its termination will be assumed for verification purposes, not checked
  Verification successful.
