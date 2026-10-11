  $ dune exec -- raven --shh ./witness_wrong_constructor_selector.rav
  [Error] File "./witness_wrong_constructor_selector.rav", line 8, columns 9-32:
  8 |   exhale own(x.f, busy(7).value);
               ^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: This assertion may not hold: insufficient permissions.
  [Error] File "./witness_wrong_constructor_selector.rav", line 8, columns 9-32:
  8 |   exhale own(x.f, busy(7).value);
               ^^^^^^^^^^^^^^^^^^^^^^^
  Related Location: This own predicate may not hold.
  [1]
