  $ dune exec -- raven --shh ./ghost_reference_read.rav
  [Error] File "./ghost_reference_read.rav", line 7, columns 14-15:
  7 |   ordinary := x.integer;
                    ^
  Type Error: This expression reads ghost state, so it can only be used inside a ghost block, spec, or ghost-typed field.
  [1]
