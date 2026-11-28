  $ dune exec -- raven --shh ./implicit_returns_fail.rav
  [Error] File "./implicit_returns_fail.rav", line 12, columns 2-15:
  12 |   r := pair(v);
         ^^^^^^^^^^^^^
  Type Error: pair has 2 return parameter(s), but found 1 return variable(s).
  [1]
