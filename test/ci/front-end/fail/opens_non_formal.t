  $ dune exec -- raven --shh ./opens_non_formal.rav
  [Error] File "./opens_non_formal.rav", line 14, columns 13-14:
  14 |   opens cell(r)
                    ^
  Type Error: r cannot be used in an opens clause; arguments may only mention the callable's formals.
  [1]
