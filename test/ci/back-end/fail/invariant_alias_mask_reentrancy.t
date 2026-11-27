  $ dune exec -- raven --shh ./invariant_alias_mask_reentrancy.rav
  [Error] File "./invariant_alias_mask_reentrancy.rav", line 30, columns 7-14:
  30 | module Applied = Worker[Actual]
              ^^^^^^^
  Type Error: Cannot establish invariant namespace separation between cell and Actual.shared.
  [Error] File "./invariant_alias_mask_reentrancy.rav", line 26, columns 4-17:
  26 |     P.consume(x);
           ^^^^^^^^^^^^^
  Related Location: This generic check requires the namespaces to be disjoint.
  [1]
