  $ dune exec -- raven --shh ./seq_of_list.rav
  [Error] File "./seq_of_list.rav", line 5, columns 9-37:
  5 |   assert S.length(S.of_list(xs)) == 1;
               ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: This assertion may be violated.
  [Error] File "./seq_of_list.rav", line 10, columns 9-39:
  10 |   assert S.index(S.of_list(xs), 0) == 7;
                ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: This assertion may be violated.
  [1]
