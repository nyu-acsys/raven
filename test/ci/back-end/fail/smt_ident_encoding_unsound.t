  $ dune exec -- raven --shh ./smt_ident_encoding_unsound.rav
  [Error] File "./smt_ident_encoding_unsound.rav", line 3, columns 9-69:
  3 |   assert forall value': Int :: forall value_: Int :: value' == value_;
               ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: This assertion may be violated.
  [1]
