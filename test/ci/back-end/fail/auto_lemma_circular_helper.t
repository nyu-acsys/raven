  $ dune exec -- raven --shh ./auto_lemma_circular_helper.rav
  [Error] File "./auto_lemma_circular_helper.rav", line 19, columns 25-25:
  19 |   lemma length_nonneg_rec(s: T)
                                ^
  Verification Error: A postcondition may not hold at this return point.
  [Error] File "./auto_lemma_circular_helper.rav", line 20, columns 12-26:
  20 |     ensures 0 <= length(s)
                   ^^^^^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]
