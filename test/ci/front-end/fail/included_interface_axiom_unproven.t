  $ dune exec -- raven --shh ./included_interface_axiom_unproven.rav
  [Error] File "included/mini_ra.rav", line 10, columns 13-24:
  10 |   auto axiom compCommute()
                    ^^^^^^^^^^^
  Related Location: Lemma compCommute inherited from axiom MiniRA.compCommute.
  [Error] File "./included_interface_axiom_unproven.rav", line 9, columns 10-10:
  9 | module Fst : MiniRA {
                ^
  Verification Error: A postcondition may not hold at this return point.
  [Error] File "included/mini_ra.rav", line 11, columns 59-83:
  11 |     ensures forall a: T, b: T :: {comp(a, b)} {comp(b, a)} comp(a, b) == comp(b, a)
                                                                  ^^^^^^^^^^^^^^^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]
