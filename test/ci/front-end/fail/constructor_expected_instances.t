  $ dune exec -- raven --shh --typeonly ./constructor_expected_instances.rav
  [Error] File "./constructor_expected_instances.rav", line 4, columns 35-39:
  4 |   val xs: Alias := Library.List.::(true, Library.List.nil);
                                         ^^^^
  Type Error: Expected an expression of type
    Int
  but found an expression of type
    Bool.
  [1]
