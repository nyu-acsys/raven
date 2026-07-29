  $ dune exec -- raven --shh ./assert_with_bad_witness.rav
  [Error] File "./assert_with_bad_witness.rav", line 4, columns 26-32:
  4 |   assert exists x: Int :: x > 10 with {
                                ^^^^^^
  Verification Error: This assertion may be violated.
  [1]
