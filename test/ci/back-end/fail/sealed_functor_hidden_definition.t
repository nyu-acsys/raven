  $ dune exec -- raven --shh ./sealed_functor_hidden_definition.rav
  [Error] File "./sealed_functor_hidden_definition.rav", line 32, columns 11-42:
  32 |     assert S.size(S.push(S.empty, 1)) == 1;
                  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: This assertion may be violated.
  [1]
