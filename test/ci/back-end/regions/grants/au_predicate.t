  $ dune exec -- raven --shh ./au_predicate.rav
  [Error] Type Error: Cannot establish invariant namespace separation between root and dependencies(stored)
  [Error] File "./au_predicate.rav", line 25, columns 2-10:
  25 |   step(x);
         ^^^^^^^^
  Related Location: This generic check requires the namespaces to be disjoint.
  [1]
