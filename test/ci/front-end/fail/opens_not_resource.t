  $ dune exec -- raven --shh ./opens_not_resource.rav
  [Error] File "./opens_not_resource.rav", line 18, columns 8-9:
  18 |   opens p(x)
               ^
  Type Error: Expected a predicate or invariant in this opens clause, but found function p.
  [1]
