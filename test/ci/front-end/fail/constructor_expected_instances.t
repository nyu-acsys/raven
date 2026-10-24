  $ dune exec -- raven --shh --typeonly ./constructor_expected_instances.rav
  [Error] File "./constructor_expected_instances.rav", line 4, columns 35-39:
  4 |   val xs: Alias := Library.List.::(true, Library.List.nil);
                                         ^^^^
  Type Error: Expected an expression of type
    Int
  but found an expression of type
    Bool.
  [Error] File "./constructor_expected_instances.rav", line 8, columns 38-47:
  8 |   val xs: Alias := Library.List.::(2, canonical);
                                            ^^^^^^^^^
  Type Error: Expected an expression of type
    Named.T
  but found an expression of type
    Library.List[Int].
  
  Named.T and Library.List[Int] come from two separately declared instances of Library.List with the same arguments. A declared instance has its own types, even when its arguments are those of another instance. Declare the instance once and use it in both places.
  [Error] File "./constructor_expected_instances.rav", line 11, columns 38-60:
  11 |   val canonical: Library.List[Int] := Named.::(1, Named.nil);
                                             ^^^^^^^^^^^^^^^^^^^^^^
  Type Error: Expected an expression of type
    Library.List[Int]
  but found an expression of type
    Named.T.
  
  Library.List[Int] and Named.T come from two separately declared instances of Library.List with the same arguments. A declared instance has its own types, even when its arguments are those of another instance. Declare the instance once and use it in both places.
  [1]
