  $ dune exec -- raven --shh cut.rav
  [Error] File "cut.rav", line 8, columns 2-11:
  8 |   y.f := 0;
        ^^^^^^^^^
  Verification Error: Could not assert sufficient permissions to assign this field.
  [Error] File "cut.rav", line 17, columns 9-15:
  17 |   assert v == 1;
                ^^^^^^
  Verification Error: This assertion may be violated.
  [Error] File "cut.rav", line 25, columns 9-10:
  25 |   assert c;
                ^
  Verification Error: This assertion may be violated.
  [Error] File "cut.rav", line 31, columns 6-22:
  31 |   cut own(x.f, 2, 1.0);
             ^^^^^^^^^^^^^^^^
  Verification Error: The cut's assertion may not hold.
  [Error] File "cut.rav", line 31, columns 6-22:
  31 |   cut own(x.f, 2, 1.0);
             ^^^^^^^^^^^^^^^^
  Related Location: This own predicate may not hold.
  [1]
  $ dune exec -- raven --shh cut_open.rav
  [Error] File "cut_open.rav", line 11, columns 2-11:
  11 |   cut true;
         ^^^^^^^^^
  Verification Error: A cut cannot be made while an invariant or atomic update is open.
  [1]
