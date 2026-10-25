  $ dune exec -- raven --shh ./ssa_state.rav
  [Error] File "./ssa_state.rav", line 7, columns 9-15:
  7 |   assert y == 2;
               ^^^^^^
  Verification Error: This assertion may be violated.
  [Error] File "./ssa_state.rav", line 17, columns 9-15:
  17 |   assert x == 1;
                ^^^^^^
  Verification Error: This assertion may be violated.
  [Error] File "./ssa_state.rav", line 23, columns 9-15:
  23 |   assert x == 0;
                ^^^^^^
  Verification Error: This assertion may be violated.
  [Error] File "./ssa_state.rav", line 29, columns 9-15:
  29 |   assert x == 5;
                ^^^^^^
  Verification Error: This assertion may be violated.
  [Error] File "./ssa_state.rav", line 37, columns 9-15:
  37 |   assert x == 6;
                ^^^^^^
  Verification Error: This assertion may be violated.
  [1]
