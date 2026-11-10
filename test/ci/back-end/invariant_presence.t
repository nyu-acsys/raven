Established no-output invariants remain duplicable across calls, folds, unfolds,
iterated separating conjunctions, and fused heap transfers.

  $ raven --shh invariant_presence.rav
  Verification successful.

The presence algebra's laws are proved by the library tests without adding
automatic axioms to these verification queries.

  $ raven --shh --verbosity=debug invariant_presence.rav > debug.out 2>&1
  $ grep -c '^; Auto lemma: \$Lowering.UnitAgree\.' log.smt2
  0
  [1]
