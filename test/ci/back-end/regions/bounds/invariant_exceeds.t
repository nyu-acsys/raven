  $ dune exec -- raven --shh ./invariant_exceeds.rav
  [Error] File "./invariant_exceeds.rav", line 6, columns 7-12:
  6 | module Cells : Frozen {
             ^^^^^
  Type Error: Incompatible module namespace contracts: the invariants frozen depends on exceed its depends clause.
  [1]
