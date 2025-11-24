  $ dune exec -- raven --shh ./arc_buggy.rav
  [Error] File "./arc_buggy.rav", line 131, columns 12-27:
  131 |             fold arcInv(x);
                    ^^^^^^^^^^^^^^^
  Verification Error: Failed to fold predicate. The body of the predicate may not hold at this point.
  [Error] File "./arc_buggy.rav", line 23, columns 49-67:
  23 |         exists v: Int :: (v <= 0 ? noTokens(x) : tokenCounter(x, v)) && own(x.c, v, 1.0)
                                                        ^^^^^^^^^^^^^^^^^^
  Related Location: This predicate may not hold.
  [1]
