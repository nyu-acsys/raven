  $ dune exec -- raven --shh ./exceeds.rav
  [Error] File "./exceeds.rav", line 6, columns 7-13:
  6 | module Actual : Context {
             ^^^^^^
  Type Error: Incompatible module namespace contracts: the invariants context depends on exceed its depends clause.
  [1]
