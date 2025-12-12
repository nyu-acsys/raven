  $ dune exec -- raven --shh ./adt_buggy.rav
  [Error] File "./adt_buggy.rav", line 76, column 11 to line 81, column 13:
  76 |     assert !is_nil(xs)
                  ^^^^^^^^^^^
  Verification Error: This assertion may be violated.
  [1]
