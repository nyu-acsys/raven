  $ dune exec -- raven --shh ./au_candidate.rav
  [Error] Type Error: Cannot establish invariant namespace separation between root and dependencies(host)
  [Error] File "./au_candidate.rav", line 23, columns 2-10:
  23 |   step(x);
         ^^^^^^^^
  Related Location: This generic check requires the namespaces to be disjoint.
  [1]
