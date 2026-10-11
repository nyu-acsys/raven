  $ dune exec -- raven --shh ./assertion_labels_fail_pure.rav
  [Error] File "./assertion_labels_fail_pure.rav", line 3, columns 17-22:
  3 |   assert bounds: false;
                       ^^^^^
  Verification Error: Assertion 'bounds': This assertion may be violated.
  [1]
