  $ dune exec -- raven --shh ./half_requires.rav
  [Error] File "./half_requires.rav", line 9, columns 5-9:
  9 | func half(n: Int) returns (r: Int)
           ^^^^
  Type Error: half may not have a requires clause; func/pred/invariant contracts must be total.
  [1]
