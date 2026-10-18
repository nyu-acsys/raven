  $ dune exec -- raven --shh callee_same_names.rav
  [Error] File "callee_same_names.rav", line 14, columns 9-14:
  14 |   assert false;
                ^^^^^
  Verification Error: This assertion may be violated.
  [Error] File "callee_same_names.rav", line 29, columns 9-14:
  29 |   assert false;
                ^^^^^
  Verification Error: This assertion may be violated.
  [Error] File "callee_same_names.rav", line 37, columns 9-14:
  37 |   assert false;
                ^^^^^
  Verification Error: This assertion may be violated.
  [Error] File "callee_same_names.rav", line 49, columns 9-14:
  49 |   assert false;
                ^^^^^
  Verification Error: This assertion may be violated.
  [Error] File "callee_same_names.rav", line 57, columns 9-16:
  57 |   exhale q(a, b);
                ^^^^^^^
  Verification Error: This assertion may not hold: insufficient permissions.
  [Error] File "callee_same_names.rav", line 57, columns 9-16:
  57 |   exhale q(a, b);
                ^^^^^^^
  Related Location: This predicate may not hold.
  [Error] File "callee_same_names.rav", line 64, columns 9-14:
  64 |   assert false;
                ^^^^^
  Verification Error: This assertion may be violated.
  [Error] File "callee_same_names.rav", line 76, columns 9-14:
  76 |   assert false;
                ^^^^^
  Verification Error: This assertion may be violated.
  [Error] File "callee_same_names.rav", line 90, columns 9-14:
  90 |   assert false;
                ^^^^^
  Verification Error: This assertion may be violated.
  [1]
