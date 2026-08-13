  $ dune exec -- raven --shh ./no_injectivity.rav
  [Error] File "./no_injectivity.rav", line 31, columns 13-110:
  31 |     requires forall j: Int :: {S.loc(s, j)} 0 <= j && j < S.size(s) ==> own(S.loc(s, j).count, counts[j], 1.0)
                    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: Could not prove the injectivity of the index expression for this iterated separating conjunction.
  [1]
