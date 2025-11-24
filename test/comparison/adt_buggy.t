  $ dune exec -- raven --shh ./adt_buggy.rav
  [Error] File "./adt_buggy.rav", line 75, column 11 to line 80, column 13:
  75 |     assert !is_nil(xs)
                  ^^^^^^^^^^^
  Verification Error: This assertion may be violated.
  [1]
