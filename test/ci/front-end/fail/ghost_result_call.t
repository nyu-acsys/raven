  $ dune exec -- raven --shh ./ghost_result_call.rav
  [Error] File "./ghost_result_call.rav", line 11, columns 2-3:
  11 |   k := g(x, 3);
         ^
  Type Error: This expression reads ghost state, so it can only be used inside a ghost block, spec, or ghost-typed field.
  [1]
