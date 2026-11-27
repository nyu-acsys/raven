  $ dune exec -- raven --shh ./namespace_instance_separation.rav
  [Error] File "./namespace_instance_separation.rav", line 28, columns 7-14:
  28 | module Applied = Worker[Actual]
              ^^^^^^^
  Verification Error: Cannot establish invariant namespace separation between cell(y) and cell(x).
  [Error] File "./namespace_instance_separation.rav", line 24, columns 4-15:
  24 |     P.touch(x);
           ^^^^^^^^^^^
  Related Location: This generic check requires the namespaces to be disjoint.
  [1]
