  $ dune exec -- raven --shh ./namespace_instances.rav
  [Error] File "./namespace_instances.rav", line 27, columns 7-14:
  27 | module Applied = Worker[Actual]
              ^^^^^^^
  Type Error: Cannot establish invariant namespace separation between cell and Actual.shared.
  [Error] File "./namespace_instances.rav", line 23, columns 4-15:
  23 |     P.touch(x);
           ^^^^^^^^^^^
  Related Location: This generic check requires the namespaces to be disjoint.
  [1]
