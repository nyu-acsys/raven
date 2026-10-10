  $ dune exec -- raven --shh heap_point_updates.rav
  Verification successful.
  $ dune exec -- raven --shh --no-heap-fusion heap_point_updates.rav
  Verification successful.
  $ dune exec -- raven --shh --verbosity=debug heap_point_updates.rav > /dev/null 2>&1
  $ awk '/^[[:space:]]*proc fractions\(/ { active=1 } /^[[:space:]]*proc lattice_exhales\(/ { active=0 } active && /heapChunk(Comp|Frame|Compare)\(/ { n++ } END { print "Generic operations in specialized procedures:", n+0 }' lowered_output.log
  Generic operations in specialized procedures: 0
  $ awk '/^[[:space:]]*proc persistent_exhales\(/ { active=1 } /^[[:space:]]*proc incompatible_persistent\(/ { active=0 } active && /map_update/ { n++ } END { print "Invariant updates (initial inhale only):", n+0 }' lowered_output.log
  Invariant updates (initial inhale only): 1
  $ awk '/^[[:space:]]*proc incompatible_persistent\(/ { active=1 } /^[[:space:]]*proc overfull_inhale\(/ { active=0 } active && /map_update/ { n++ } END { print "Changed invariant pair updates (initial inhale only):", n+0 }' lowered_output.log
  Changed invariant pair updates (initial inhale only): 1
  $ awk '/^[[:space:]]*proc lattice_exhales\(/ { active=1 } /^[[:space:]]*proc lattice_pair\(/ { active=0 } active && /map_update/ { n++ } END { print "Lattice updates (two initial inhales only):", n+0 }' lowered_output.log
  Lattice updates (two initial inhales only): 2
  $ awk '/^[[:space:]]*proc repeated\(/ { active=1 } active && /map_update/ { n++ } END { print "Abstract lattice updates (initial inhale only):", n+0 }' lowered_output.log
  Abstract lattice updates (initial inhale only): 1
