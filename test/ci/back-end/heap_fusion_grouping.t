  $ dune exec -- raven --shh ./heap_fusion_grouping.rav
  Verification successful.

Each of the four procedures fuses its pair of transfers, which the debug log of the
lowered program records once per pair.

  $ dune exec -- raven --verbosity=debug ./heap_fusion_grouping.rav > /dev/null 2>&1
  $ grep -c "Fused .*: inhale validity" lowered_output.log
  4
