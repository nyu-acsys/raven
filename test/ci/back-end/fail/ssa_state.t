  $ dune exec -- raven --shh ./ssa_state.rav
  [Error] File "./ssa_state.rav", line 7, columns 9-15:
  7 |   assert y == 2;
               ^^^^^^
  Verification Error: This assertion may be violated.
  [Error] File "./ssa_state.rav", line 17, columns 9-15:
  17 |   assert x == 1;
                ^^^^^^
  Verification Error: This assertion may be violated.
  [Error] File "./ssa_state.rav", line 24, columns 9-15:
  24 |   assert x == 0;
                ^^^^^^
  Verification Error: This assertion may be violated.
  [Error] File "./ssa_state.rav", line 30, columns 9-15:
  30 |   assert x == 5;
                ^^^^^^
  Verification Error: This assertion may be violated.
  [Error] File "./ssa_state.rav", line 38, columns 9-15:
  38 |   assert x == 6;
                ^^^^^^
  Verification Error: This assertion may be violated.
  [1]
