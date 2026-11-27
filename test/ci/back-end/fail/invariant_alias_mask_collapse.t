  $ dune exec -- raven --shh ./invariant_alias_mask_collapse.rav
  [Error] File "./invariant_alias_mask_collapse.rav", line 24, columns 7-14:
  24 | module Applied = Worker[Actual]
              ^^^^^^^
  Type Error: Cannot establish invariant namespace separation between Actual.first and Actual.second.
  [Error] File "./invariant_alias_mask_collapse.rav", line 18, columns 4-23:
  18 |     unfold P.second(x);
           ^^^^^^^^^^^^^^^^^^^
  Related Location: This generic check requires the namespaces to be disjoint.
  [1]
