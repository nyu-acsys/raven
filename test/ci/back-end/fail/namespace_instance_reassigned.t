  $ dune exec -- raven --shh ./namespace_instance_reassigned.rav
  [Error] File "./namespace_instance_reassigned.rav", line 29, columns 7-14:
  29 | module Applied = Worker[Actual]
              ^^^^^^^
  Type Error: Cannot establish invariant namespace separation between cell and Actual.shared.
  [Error] File "./namespace_instance_reassigned.rav", line 25, columns 4-15:
  25 |     P.touch(x);
           ^^^^^^^^^^^
  Related Location: This generic check requires the namespaces to be disjoint.
  [1]
