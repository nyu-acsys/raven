  $ dune exec -- raven --shh heap_point_value.rav 2>&1 | grep '^Verification Error:'
  Verification Error: This assertion may not hold: insufficient permissions.
  $ dune exec -- raven --shh heap_point_lattice.rav 2>&1 | grep '^Verification Error:'
  Verification Error: This assertion may not hold: insufficient permissions.
  $ dune exec -- raven --shh heap_point_guard.rav 2>&1 | grep '^Verification Error:'
  Verification Error: This assertion may be violated.
