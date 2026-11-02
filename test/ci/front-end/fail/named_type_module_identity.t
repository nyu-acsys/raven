  $ dune exec -- raven --shh --typeonly ./named_type_module_identity.rav
  [Error] File "./named_type_module_identity.rav", line 5, columns 12-18:
  5 |   result := values;
                  ^^^^^^
  Type Error: Expected an expression of type
    Library.List[B]
  but found an expression of type
    Library.List[A].
  [1]
