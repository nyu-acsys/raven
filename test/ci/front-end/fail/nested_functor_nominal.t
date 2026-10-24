  $ dune exec -- raven --shh --typeonly ./nested_functor_nominal.rav
  [Error] File "./nested_functor_nominal.rav", line 12, columns 18-19:
  12 |   val y: Right := x;
                         ^
  Type Error: Expected an expression of type
    Right.T
  but found an expression of type
    Left.T.
  
  Right.T and Left.T come from two separately declared instances of Outer.Inner with the same arguments. A declared instance has its own types, even when its arguments are those of another instance. Declare the instance once and use it in both places.
  [Error] File "./nested_functor_nominal.rav", line 17, columns 38-39:
  17 |   val y: OtherOuterInt.Inner[Bool] := x;
                                             ^
  Type Error: Expected an expression of type
    OtherOuterInt.Inner[Bool]
  but found an expression of type
    OuterInt.Inner[Bool].
  
  OtherOuterInt.Inner[Bool] and OuterInt.Inner[Bool] come from two separately declared instances of Outer.Inner with the same arguments. A declared instance has its own types, even when its arguments are those of another instance. Declare the instance once and use it in both places.
  [1]
