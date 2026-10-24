  $ dune exec -- raven --shh --typeonly ./recursive_datatypes.rav
  [Error] File "./recursive_datatypes.rav", line 11, columns 18-19:
  11 |   val y: Right := x;
                         ^
  Type Error: Expected an expression of type
    Right.T
  but found an expression of type
    Left.T.
  
  Right.T and Left.T come from two separately declared instances of Rose with the same arguments. A declared instance has its own types, even when its arguments are those of another instance. Declare the instance once and use it in both places.
  [1]
