  $ dune exec -- raven --shh ./type_default_unspecified.rav
  [Error] File "./type_default_unspecified.rav", line 8, columns 1-1:
  8 | }
       ^
  Verification Error: A postcondition may not hold at this return point.
  [Error] File "./type_default_unspecified.rav", line 6, columns 10-34:
  6 |   ensures IntOption.E.default == 0
                ^^^^^^^^^^^^^^^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]
