  $ dune exec -- raven --shh --typeonly ./invariant_within.rav > diagnostics 2>&1
  [1]
  $ sed -n '/^Type Error:/p' diagnostics
  Type Error: A within argument must be an explicit parameter of the child invariant.
  Type Error: A within argument must be an explicit parameter of the child invariant.
  Type Error: Expected an expression of type
  Type Error: A within clause must name an invariant.
  Type Error: Only invariants may declare a within clause.
