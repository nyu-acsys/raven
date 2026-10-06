  $ dune exec -- raven --shh ./smt_reserved_names_unsound.rav
  [Error] File "./smt_reserved_names_unsound.rav", line 9, columns 9-31:
  9 |   assert {|1|} ++ {|2|} == {||};
               ^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: This assertion may be violated.
  [1]
