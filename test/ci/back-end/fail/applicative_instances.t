  $ dune exec -- raven --shh ./applicative_duplicate_field.rav
  [Error] File "./applicative_duplicate_field.rav", line 11, columns 1-1:
  11 | }
        ^
  Verification Error: A postcondition may not hold at this return point.
  [Error] File "./applicative_duplicate_field.rav", line 9, columns 32-50:
  9 |   ensures own(x.A.f, n, 1.0) && own(x.B.f, n, 1.0)
                                      ^^^^^^^^^^^^^^^^^^
  Related Location: This own predicate may not hold.
  [1]

  $ dune exec -- raven --shh ./applicative_invalid_body.rav
  [Error] File "./applicative_invalid_body.rav", line 6, columns 3-3:
  6 |   }
         ^
  Verification Error: A postcondition may not hold at this return point.
  [Error] File "./applicative_invalid_body.rav", line 3, columns 12-18:
  3 |     ensures r == 0
                  ^^^^^^
  Related Location: This assertion may not hold.
  [1]
