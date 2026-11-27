  $ dune exec -- raven --shh ./opaque_predicate.rav
  [Error] File "./opaque_predicate.rav", line 16, columns 2-18:
  16 |   Actual.touch(x);
         ^^^^^^^^^^^^^^^^
  Verification Error: Cannot call touch. The invariant hidden required by touch is not available in the current mask.
  [1]
