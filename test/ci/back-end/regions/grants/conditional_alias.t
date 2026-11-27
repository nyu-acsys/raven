  $ dune exec -- raven --shh ./conditional_alias.rav
  [Error] File "./conditional_alias.rav", line 22, columns 7-11:
  22 | module Risk = Client[Hidden]
              ^^^^
  Type Error: Cannot establish invariant namespace separation between root and dependencies(Hidden.p).
  [Error] File "./conditional_alias.rav", line 1, columns 4-8:
  1 | inv root(x: Int) { true }
          ^^^^
  Related Location: This generic check requires the namespaces to be disjoint.
  [1]
