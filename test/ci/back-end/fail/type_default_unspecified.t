  $ dune exec -- raven --shh ./type_default_unspecified.rav
  [Error] File "./type_default_unspecified.rav", line 6, columns 1-1:
  6 | }
       ^
  Verification Error: A postcondition may not hold at this return point.
  [Error] File "./type_default_unspecified.rav", line 4, columns 10-38:
  4 |   ensures Library.IntType.default == 0
                ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]
