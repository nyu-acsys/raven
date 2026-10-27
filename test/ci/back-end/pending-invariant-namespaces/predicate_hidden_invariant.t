  $ dune exec -- raven --shh ./predicate_hidden_invariant.rav
  [Error] File "./predicate_hidden_invariant.rav", line 8, columns 7-13:
  8 | module Actual : Resource {
             ^^^^^^
  Type Error: The implementation of abstract predicate Resource.resource introduces invariant dependencies cell.
  [1]
