  $ dune exec -- raven --shh ./namespace_separation.rav
  [Error] File "./namespace_separation.rav", line 43, columns 7-14:
  43 | module Applied = Worker[Actual]
              ^^^^^^^
  Verification Error: Cannot establish invariant namespace separation between cell(y) and cell(root).
  [Error] File "./namespace_separation.rav", line 38, columns 4-15:
  38 |     P.touch(x);
           ^^^^^^^^^^^
  Related Location: This generic check requires the namespaces to be disjoint.
  [1]
