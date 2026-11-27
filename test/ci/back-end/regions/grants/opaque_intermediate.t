  $ dune exec -- raven --shh ./opaque_intermediate.rav
  [Error] File "./opaque_intermediate.rav", line 18, columns 7-11:
  18 | module Risk = Client[Hidden]
              ^^^^
  Type Error: Cannot establish invariant namespace separation between root and dependencies(Hidden.p).
  [Error] File "./opaque_intermediate.rav", line 12, columns 4-19:
  12 |     unfold root(x);
           ^^^^^^^^^^^^^^^
  Related Location: This generic check requires the namespaces to be disjoint.
  [1]
