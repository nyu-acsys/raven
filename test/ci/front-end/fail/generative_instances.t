  $ dune exec -- raven --shh ./generative_instances.rav
  [Error] File "./generative_instances.rav", line 10, columns 9-10:
  10 |     b := a;
                ^
  Type Error: Expected an expression of type
    B.U
  but found an expression of type
    A.U.
  
  B.U and A.U come from two separately declared instances of F with the same arguments. A declared instance has its own types, even when its arguments are those of another instance. Declare the instance once and use it in both places.
  [1]
