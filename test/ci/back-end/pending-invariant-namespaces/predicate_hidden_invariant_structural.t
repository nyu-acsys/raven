  $ dune exec -- raven --shh ./predicate_hidden_invariant_structural.rav
  [Error] File "./predicate_hidden_invariant_structural.rav", line 13, columns 7-15:
  13 | module Selected : Resource = checked Actual
              ^^^^^^^^
  Type Error: The implementation of abstract predicate Resource.resource introduces invariant dependencies cell.
  [1]
