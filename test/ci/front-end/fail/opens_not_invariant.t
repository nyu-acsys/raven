  $ dune exec -- raven --shh ./opens_not_invariant.rav
  [Error] File "./opens_not_invariant.rav", line 18, columns 8-9:
  18 |   opens p(x)
               ^
  Type Error: Expected an invariant in this opens clause, but found predicate p.
  [1]
