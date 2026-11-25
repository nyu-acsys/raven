  $ dune exec -- raven --shh ./private_ancestor.rav
  [Error] File "./private_ancestor.rav", line 2, columns 7-13:
  2 | module Actual: Family {
             ^^^^^^
  Type Error: Incompatible module namespace contracts: Realization gives invariant root Actual.root an undeclared ancestor.
  [1]
