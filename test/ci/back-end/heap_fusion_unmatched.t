  $ dune exec -- raven --shh heap_fusion_unmatched.rav
  Verification successful.
  $ dune exec -- raven --shh --no-heap-fusion heap_fusion_unmatched.rav
  Verification successful.
  $ dune exec -- raven --shh --verbosity=debug heap_fusion_unmatched.rav > /dev/null 2>&1
  $ grep -c 'Fused exhale/inhale: consumption check' lowered_output.log
  0
  [1]
