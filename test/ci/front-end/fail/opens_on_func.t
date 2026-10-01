  $ dune exec -- raven --shh ./opens_on_func.rav
  [Error] File "./opens_on_func.rav", line 12, columns 5-6:
  12 | func g(x: Int) returns (r: Int)
            ^
  Type Error: g may not have an opens clause; only procedures and lemmas can.
  [1]
