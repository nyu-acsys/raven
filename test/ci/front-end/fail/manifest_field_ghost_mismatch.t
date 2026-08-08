  $ dune exec -- raven --shh ./manifest_field_ghost_mismatch.rav
  [Error] File "./manifest_field_ghost_mismatch.rav", line 7, columns 10-22:
  7 | module M { field f = g }
                ^^^^^^^^^^^^
  Type Error: Field f is declared non-ghost, but g is ghost.
  [1]
