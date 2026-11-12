  $ dune exec -- raven --shh ./namespace_instances.rav
  [Error] File "./namespace_instances.rav", line 28, columns 7-14:
  28 | module Applied = Worker[Actual]
              ^^^^^^^
  Type Error: Cannot establish invariant namespace separation between cell and Actual.shared.
  [Error] File "./namespace_instances.rav", line 24, columns 4-15:
  24 |     P.touch(x);
           ^^^^^^^^^^^
  Related Location: This generic check requires the namespaces to be disjoint.
  [1]
