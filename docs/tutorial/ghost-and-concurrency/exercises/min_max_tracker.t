  $ dune exec -- raven --shh ./min_max_tracker.rav
  [Error] File "./min_max_tracker.rav", line 85, columns 4-20:
  85 |     fold scoreInv(c)
           ^^^^^^^^^^^^^^^^
  Verification Error: Failed to fold predicate. The body of the predicate may not hold at this point.
  [Error] File "./min_max_tracker.rav", line 29, columns 29-62:
  29 |     && own(c.low, l, 1.0) && own(c.seenLow, auth_frag(-l, -l))
                                    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Related Location: This own predicate may not hold.
  [1]
