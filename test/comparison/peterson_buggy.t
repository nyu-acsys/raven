  $ dune exec -- raven --shh ./peterson_buggy.rav
  [Error] File "./peterson_buggy.rav", line 207, column 8 to line 213, column 10:
  207 |         fold peterson_inv(l, r)[
                ^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: Failed to fold predicate. The body of the predicate may not hold at this point.
  [Error] File "./peterson_buggy.rav", line 25, columns 12-37:
  25 |             own(l.wait_left, wl, 0.5)
                   ^^^^^^^^^^^^^^^^^^^^^^^^^
  Related Location: This own predicate may not hold.
  [1]
