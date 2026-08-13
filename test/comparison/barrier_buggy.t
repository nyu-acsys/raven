  $ dune exec -- raven --shh ./barrier_buggy.rav
  [Error] File "./barrier_buggy.rav", line 286, columns 12-34:
  286 |             fold is_barrier(l, r);
                    ^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: Failed to fold predicate. The body of the predicate may not hold at this point.
  [Error] File "./barrier_buggy.rav", line 111, columns 12-25:
  111 |             own(l.ctr, z)
                    ^^^^^^^^^^^^^
  Related Location: This own predicate may not hold.
  [1]
