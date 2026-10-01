  $ dune exec -- raven --shh ./opens_arity.rav
  [Error] File "./opens_arity.rav", line 15, columns 8-12:
  15 |   opens pair(x)
               ^^^^
  Type Error: Invariant pair takes 2 argument(s), but 1 are given here; write `_` for an argument left unspecified.
  [1]
