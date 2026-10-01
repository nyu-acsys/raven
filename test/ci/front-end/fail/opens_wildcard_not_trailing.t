  $ dune exec -- raven --shh ./opens_wildcard_not_trailing.rav
  [Error] File "./opens_wildcard_not_trailing.rav", line 14, columns 16-17:
  14 |   opens pair(_, y)
                       ^
  Syntax Error: In an opens clause, `_` may only stand for trailing arguments.
  [1]
