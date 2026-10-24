  $ dune exec -- raven --shh ./recursive_datatypes.rav
  [Error] File "./recursive_datatypes.rav", line 11, columns 9-38:
  11 |   assert parent.children.hd.value == 2;
                ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: This assertion may be violated.
  [1]
