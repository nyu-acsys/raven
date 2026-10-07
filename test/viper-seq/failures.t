  $ dune exec -- raven --shh ./failures/sequences_t1.rav
  [Error] File "./failures/sequences_t1.rav", line 3, columns 9-31:
  3 |   assert Seq.length([|0|]) == 0;
               ^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: This assertion may be violated.
  [1]
  $ dune exec -- raven --shh ./failures/sequences_t2.rav
  [Error] File "./failures/sequences_t2.rav", line 4, columns 9-28:
  4 |   assert a[1 := 22][0] == 22;
               ^^^^^^^^^^^^^^^^^^^
  Verification Error: This assertion may be violated.
  [1]
  $ dune exec -- raven --shh ./failures/sequences_test3.rav
  [Error] File "./failures/sequences_test3.rav", line 4, columns 9-46:
  4 |   assert Seq.length(xs[1..]) == Seq.length(xs);
               ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: This assertion may be violated.
  [1]
  $ dune exec -- raven --shh ./failures/sequences_test4.rav
  [Error] File "./failures/sequences_test4.rav", line 6, columns 9-48:
  6 |   assert Seq.length(s[j..]) == Seq.length(s) - j;
               ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: This assertion may be violated.
  [1]
  $ dune exec -- raven --shh ./failures/sequences_test6.rav
  [Error] File "./failures/sequences_test6.rav", line 3, columns 9-31:
  3 |   assert [|3, 4, 5, 6|][3] == 5;
               ^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: This assertion may be violated.
  [1]
  $ dune exec -- raven --shh ./failures/sequence_incompletenesses_colourings1.rav
  [Error] File "./failures/sequence_incompletenesses_colourings1.rav", line 58, columns 15-35:
  58 |         assert valid(soln, n, true);
                      ^^^^^^^^^^^^^^^^^^^^
  Verification Error: This assertion may be violated.
  [1]
