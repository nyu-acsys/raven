  $ dune exec -- raven --shh ./assignment_ghost_field.rav
  [Error] File "./assignment_ghost_field.rav", line 7, columns 2-3:
  7 |   r := x.integer;
        ^
  Type Error: This expression reads ghost state, so it can only be used inside a ghost block, spec, or ghost-typed field.
  [1]
