  $ dune exec -- raven --shh ./wrong_projection.rav
  [Error] File "./wrong_projection.rav", line 6, columns 7-13:
  6 | module Actual : Family {
             ^^^^^^
  Type Error: Incompatible module namespace contracts: Realization changes the ancestry key projection from Actual.leaf to Actual.root.
  [1]
