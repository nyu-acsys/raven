  $ dune exec -- raven --shh ./assertion_labels_fail_with.rav
  [Error] File "./assertion_labels_fail_with.rav", line 3, columns 17-22:
  3 |   assert sorted: false with {
                       ^^^^^
  Verification Error: Assertion 'sorted': This assertion may be violated.
  [1]
