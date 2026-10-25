  $ dune exec -- raven --shh ./initialized_bind.rav
  [Error] File "./initialized_bind.rav", line 4, columns 9-15:
  4 |   assert x == 0;
               ^^^^^^
  Verification Error: This assertion may be violated.
  [Error] File "./initialized_bind.rav", line 11, columns 9-15:
  11 |   assert x == 7;
                ^^^^^^
  Verification Error: This assertion may be violated.
  [Error] File "./initialized_bind.rav", line 17, columns 7-27:
  17 |   x :| x == 7 && limit == 4;
              ^^^^^^^^^^^^^^^^^^^^
  Verification Error: The right-hand side of this bind statement may not hold.
  [Error] File "./initialized_bind.rav", line 23, columns 10-34:
  23 |   x, y :| x == y + 1 && y == x + 1;
                 ^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: The right-hand side of this bind statement may not hold.
  [Error] File "./initialized_bind.rav", line 28, columns 7-42:
  28 |   x :| x == 7 && (forall x: Int :: x >= 0);
              ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: The right-hand side of this bind statement may not hold.
  [Error] File "./initialized_bind.rav", line 38, columns 9-15:
  38 |   assert x == 0;
                ^^^^^^
  Verification Error: This assertion may be violated.
  [1]
