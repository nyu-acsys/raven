  $ dune exec -- raven --shh ./assertion_labels_fail_impure.rav
  [Error] File "./assertion_labels_fail_impure.rav", line 5, columns 20-31:
  5 |   assert owns_cell: own(c.f, 0);
                          ^^^^^^^^^^^
  Verification Error: Assertion 'owns_cell': This assertion may be violated.
  [Error] File "./assertion_labels_fail_impure.rav", line 5, columns 20-31:
  5 |   assert owns_cell: own(c.f, 0);
                          ^^^^^^^^^^^
  Related Location: This own predicate may not hold.
  [1]
