  $ dune exec -- raven --shh ./auto_lemma_circular_scc.rav
  [Error] File "./auto_lemma_circular_scc.rav", line 21, columns 37-37:
  21 |   { if (n > 0) { f_nonneg(n - 1); } }
                                            ^
  Verification Error: A postcondition may not hold at this return point.
  [Error] File "./auto_lemma_circular_scc.rav", line 19, columns 12-21:
  19 |     ensures f(n) >= 0
                   ^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]
