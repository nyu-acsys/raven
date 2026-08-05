  $ dune exec -- raven --shh ./no_invariant.rav
  [Error] File "./no_invariant.rav", line 38, columns 2-20:
  38 |   spawn increment(c)
         ^^^^^^^^^^^^^^^^^^
  Verification Error: A precondition may not hold for this call.
  [Error] File "./no_invariant.rav", line 21, columns 11-26:
  21 |   requires own(c.count, v)
                  ^^^^^^^^^^^^^^^
  Related Location: This own predicate may not hold.
  [1]
