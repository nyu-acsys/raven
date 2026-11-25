  $ dune exec -- raven --shh --typeonly ./invariant_ancestry.rav > diagnostics 2>&1
  [1]
  $ sed -n '/^Type Error:/p' diagnostics
  Type Error: A within clause requires an interface invariant.
  Type Error: A parent argument must be an explicit parameter of the child invariant.
  Type Error: Expected an expression of type
  Type Error: Only invariants may declare a parent clause.
