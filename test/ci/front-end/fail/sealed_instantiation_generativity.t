  $ dune exec -- raven --shh --typeonly ./sealed_instantiation_generativity.rav
  [Error] File "./sealed_instantiation_generativity.rav", line 17, columns 19-20:
  17 |   assert Boxes.get(b) == b.value;
                          ^
  Type Error: Expected an expression of type
    Box[Int]
  but found an expression of type
    NamedBox.T.
  
  Box[Int] and NamedBox.T come from two separately declared instances of Box with the same arguments. A declared instance has its own types, even when its arguments are those of another instance. Declare the instance once and use it in both places.
  [1]
