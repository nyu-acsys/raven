  $ dune exec -- raven --shh ./field_constraint_fail.rav
  [Error] File "./field_constraint_fail.rav", line 11, columns 2-19:
  11 |   c.count := v - 1;
         ^^^^^^^^^^^^^^^^^
  Verification Error: The value written may not satisfy the constraint of this field.
  [Error] File "./field_constraint_fail.rav", line 15, columns 2-22:
  15 |   c := new(count: -5);
         ^^^^^^^^^^^^^^^^^^^^
  Verification Error: Could not prove validity of initially-allocated value.
  [1]
