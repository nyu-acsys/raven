  $ dune exec -- raven --shh ./ghost_leak.rav
  [Error] File "./ghost_leak.rav", line 21, columns 6-19:
  21 |   if (predictedNext > 0) {
             ^^^^^^^^^^^^^
  Type Error: This expression reads ghost state, so it can only be used inside a ghost block, spec, or ghost-typed field.
  [1]
