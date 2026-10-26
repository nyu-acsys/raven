  $ dune exec -- raven --shh ./sealed_functor_alias_law_origin.rav
  [Error] File "./sealed_functor_alias_law_origin.rav", line 4, columns 13-21:
  4 |   auto lemma positive(x: Int) ensures forward(x) > 0
                   ^^^^^^^^
  Related Location: Contract inherited from axiom Signature.positive.
  [Error] File "./sealed_functor_alias_law_origin.rav", line 7, columns 28-28:
  7 |   lemma positive(x: Int) { }
                                  ^
  Verification Error: A postcondition may not hold at this return point.
  [Error] File "./sealed_functor_alias_law_origin.rav", line 4, columns 38-52:
  4 |   auto lemma positive(x: Int) ensures forward(x) > 0
                                            ^^^^^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]
