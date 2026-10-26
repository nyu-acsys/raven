  $ dune exec -- raven --shh ./sealed_functor_alias.rav
  [Error] File "./sealed_functor_alias.rav", line 2, columns 13-23:
  2 |   auto lemma impossible() ensures false
                   ^^^^^^^^^^
  Related Location: Contract inherited from axiom FalseLaw.impossible.
  [Error] File "./sealed_functor_alias.rav", line 5, columns 24-24:
  5 |   lemma impossible() { }
                              ^
  Verification Error: A postcondition may not hold at this return point.
  [Error] File "./sealed_functor_alias.rav", line 2, columns 34-39:
  2 |   auto lemma impossible() ensures false
                                        ^^^^^
  Related Location: This assertion may not hold.
  [1]
