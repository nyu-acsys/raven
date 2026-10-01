  $ dune exec -- raven --shh ./opens_atomic_implicit.rav
  [Error] File "./opens_atomic_implicit.rav", line 16, columns 16-17:
  16 |   opens pair(x, y)
                       ^
  Type Error: y cannot be used in an opens clause; arguments may only mention the callable's formals, other than implicit ones.
  [1]
