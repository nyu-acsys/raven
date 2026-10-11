  $ dune exec -- raven --shh ./witness_unknown_environment.rav
  [Warning] File "./witness_unknown_environment.rav", line 5, columns 17-29:
  5 |   ensures exists unknown: Int, n: Int ::
                       ^^^^^^^^^^^^
  No witness could be computed for unknown -- it will be treated as an arbitrary unconstrained value, which may cause later assertions about it to fail.
  Verification successful.
