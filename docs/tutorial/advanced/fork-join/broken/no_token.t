  $ dune exec -- raven --shh ./no_token.rav
  [Error] File "./no_token.rav", line 64, columns 6-14:
  64 |       return r
             ^^^^^^^^
  Verification Error: A postcondition may not hold at this return point.
  [Error] File "./no_token.rav", line 51, columns 12-23:
  51 |     ensures resource(r)
                   ^^^^^^^^^^^
  Related Location: This predicate may not hold.
  [1]
