  $ dune exec -- raven --shh ./auto_lemma_circular_scc.rav
  [Error] File "./auto_lemma_circular_scc.rav", line 17, columns 14-14:
  17 |   lemma helper(n: Int)
                     ^
  Verification Error: A postcondition may not hold at this return point.
  [Error] File "./auto_lemma_circular_scc.rav", line 19, columns 12-21:
  19 |     ensures f(n) >= 0
                   ^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]
