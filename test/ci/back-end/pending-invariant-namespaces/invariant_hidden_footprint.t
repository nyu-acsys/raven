  $ dune exec -- raven --shh ./invariant_hidden_footprint.rav
  [Error] Type Error: Cannot establish invariant namespace separation between cell and dependencies(Actual.shared)
  [Error] File "./invariant_hidden_footprint.rav", line 29, columns 4-17:
  29 |     P.consume(x);
           ^^^^^^^^^^^^^
  Related Location: This generic check requires the namespaces to be disjoint.
  [1]
