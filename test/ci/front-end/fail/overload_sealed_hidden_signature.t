  $ dune exec -- raven --shh ./overload_sealed_hidden_signature.rav
  [Error] File "./overload_sealed_hidden_signature.rav", line 13, columns 25-29:
  13 |     assert Public.select(true);
                                ^^^^
  Type Error: Expected an expression of type
    Int
  but found an expression of type
    Bool.
  [1]
