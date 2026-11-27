  $ dune exec -- raven --shh ./invariant_defined_formal_reentrancy.rav
  [Error] File "./invariant_defined_formal_reentrancy.rav", line 24, columns 7-14:
  24 | module Applied = Worker[Actual]
              ^^^^^^^
  Type Error: Cannot establish invariant namespace separation between Actual.shared and Actual.shared.
  [Error] File "./invariant_defined_formal_reentrancy.rav", line 20, columns 4-17:
  20 |     P.consume(x);
           ^^^^^^^^^^^^^
  Related Location: This generic check requires the namespaces to be disjoint.
  [1]
