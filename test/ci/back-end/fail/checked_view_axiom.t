  $ dune exec -- raven --shh ./checked_view_axiom.rav
  [Error] File "./checked_view_axiom.rav", line 3, columns 7-11:
  3 | module View : Required = checked Actual
             ^^^^
  Verification Error: A precondition may not hold for this call.
  [Error] File "./checked_view_axiom.rav", line 2, columns 37-42:
  2 | module Actual { lemma law() requires false ensures false { } }
                                           ^^^^^
  Related Location: This assertion may not hold.
  [1]
