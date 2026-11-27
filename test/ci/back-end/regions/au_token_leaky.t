  $ dune exec -- raven --shh ./au_token_leaky.rav
  [Error] File "./au_token_leaky.rav", line 44, columns 7-8:
  44 | module U = Client[Impl]
              ^
  Type Error: Cannot establish invariant namespace separation between counter and dependencies(Impl.resource).
  [Error] File "./au_token_leaky.rav", line 31, columns 4-13:
  31 |     touch(y);
           ^^^^^^^^^
  Related Location: This generic check requires the namespaces to be disjoint.
  [1]
