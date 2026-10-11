  $ dune exec -- raven --shh --strict ./assert_with_recursion.rav
  [Warning] File "./assert_with_recursion.rav", line 1, columns 6-13:
  1 | lemma recurse(n: Int)
            ^^^^^^^
  recurse is recursive but declares no `decreases` clause; its termination will be assumed for verification purposes, not checked
  Verification successful.
