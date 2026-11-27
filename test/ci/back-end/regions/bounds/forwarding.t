  $ dune exec -- raven --shh ./forwarding.rav
  [Error] File "./forwarding.rav", line 11, columns 7-11:
  11 | module Wrap[B: Base] : Context {
              ^^^^
  Type Error: Incompatible module namespace contracts: the invariants context depends on exceed its depends clause.
  [1]
