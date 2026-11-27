  $ dune exec -- raven --shh ./external_collision.rav
  [Error] File "./external_collision.rav", line 7, columns 7-13:
  7 | module Actual : Family {
             ^^^^^^
  Type Error: Incompatible module namespace contracts: Realization identifies distinct invariants External.root and Actual.leaf.
  [1]
