  $ dune exec -- raven --shh heap_fusion.rav
  Verification successful.
  $ dune exec -- raven --shh --no-heap-fusion heap_fusion.rav
  Verification successful.
  $ dune exec -- raven --shh --verbosity=debug heap_fusion.rav > /dev/null 2>&1
  $ awk '/Fused exhale\/inhale: consumption check/ { active=1; updates=0; next } active && /map_update/ { updates++ } /Fused exhale\/inhale: inhale validity/ && active { count[updates]++; active=0 } END { print "No updates:", count[0]; print "One update:", count[1]; print "More updates:", count[2]+0 }' lowered_output.log
  No updates: 11
  One update: 8
  More updates: 0
  $ dune exec -- raven --shh --no-heap-fusion --verbosity=debug heap_fusion.rav > /dev/null 2>&1
  $ grep -c 'Fused exhale/inhale: consumption check' lowered_output.log
  0
  [1]
