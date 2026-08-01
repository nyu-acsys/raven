  $ dune exec -- raven --shh ./stdlib_interface_axiom_unproven.rav
  [Error] File "resource_algebra.rav", line 16, columns 13-24:
  16 |   auto axiom compCommute()
                    ^^^^^^^^^^^
  Related Location: Lemma compCommute inherited from axiom Library.ResourceAlgebra.compCommute.
  [Error] File "./stdlib_interface_axiom_unproven.rav", line 7, columns 10-10:
  7 | module Fst : Library.ResourceAlgebra {
                ^
  Verification Error: A postcondition may not hold at this return point.
  [Error] File "./stdlib_interface_axiom_unproven.rav", line 7, columns 10-10:
  7 | module Fst : Library.ResourceAlgebra {
                ^
  Verification Error: A postcondition may not hold at this return point.
  [Error] File "resource_algebra.rav", line 17, columns 55-79:
  17 |     ensures forall a:T, b:T :: {comp(a,b)} {comp(b,a)} comp(a, b) == comp(b, a)
                                                              ^^^^^^^^^^^^^^^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]
