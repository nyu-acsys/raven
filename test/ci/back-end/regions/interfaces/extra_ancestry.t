  $ dune exec -- raven --shh ./extra_ancestry.rav
  [Error] File "./extra_ancestry.rav", line 6, columns 7-13:
  6 | module Actual : Independent {
             ^^^^^^
  Type Error: Incompatible module namespace contracts: Realization gives invariant root Actual.second an undeclared ancestor.
  [1]
