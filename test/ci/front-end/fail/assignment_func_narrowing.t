  $ dune exec -- raven --shh ./assignment_func_narrowing.rav
  [Error] File "./assignment_func_narrowing.rav", line 7, columns 7-17:
  7 |   r := fraction();
             ^^^^^^^^^^
  Type Error: Expected an expression of type
    Int
  but found an expression of type
    Real.
  [1]
