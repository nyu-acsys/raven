  $ dune exec -- raven --shh ./mask_opaque_hidden_dependency.rav
  [Error] File "./mask_opaque_hidden_dependency.rav", line 15, columns 23-39:
  15 |   proc touch(x: Ref) { Actual.touch(x); }
                              ^^^^^^^^^^^^^^^^
  Verification Error: Cannot call touch. The invariant hidden required by touch is not available in the current mask.
  [1]
