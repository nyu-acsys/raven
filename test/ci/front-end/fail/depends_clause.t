  $ dune exec -- raven --shh --typeonly ./depends_clause.rav > diagnostics 2>&1
  [1]
  $ sed -n '/Error:/p' diagnostics
  Type Error: Only a predicate without a definition may have a depends clause; a definition determines what the predicate depends on.
  Type Error: procedure may not have a depends clause; only predicates can.
  Type Error: shared may not have a depends clause; only predicates can.
  Error: Unknown identifier y.
  Type Error: Expected a predicate or invariant in this depends clause, but found function I.value_of.
