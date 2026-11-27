An empty procedure cannot fabricate an invariant postcondition, which would let
its caller inhale an inconsistent heap and prove false.

  $ raven --shh invariant_presence_forge.rav > forge.out 2>&1
  [1]
  $ grep -c '^Verification Error: A postcondition may not hold' forge.out
  1

Mask permission alone does not establish the invariant being unfolded. Missing
facts also fail ordinary exhale, iterated exhale, and fused exhale/inhale.

  $ raven --shh invariant_presence_missing.rav > missing.out 2>&1
  [1]
  $ grep -c '^Verification Error:' missing.out
  1
  $ raven --shh invariant_presence_unfold.rav > unfold.out 2>&1
  [1]
  $ grep -c '^Verification Error:' unfold.out
  1
  $ raven --shh invariant_presence_iterated.rav > iterated.out 2>&1
  [1]
  $ grep -c '^Verification Error:' iterated.out
  1
  $ raven --shh invariant_presence_fusion.rav > fusion.out 2>&1
  [1]
  $ grep -c '^Verification Error:' fusion.out
  1
