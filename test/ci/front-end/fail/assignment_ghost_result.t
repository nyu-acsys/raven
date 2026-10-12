  $ dune exec -- raven --shh ./assignment_ghost_result.rav
  [Error] File "./assignment_ghost_result.rav", line 9, columns 2-3:
  9 |   r := integer();
        ^
  Type Error: This expression reads ghost state, so it can only be used inside a ghost block, spec, or ghost-typed field.
  [1]
