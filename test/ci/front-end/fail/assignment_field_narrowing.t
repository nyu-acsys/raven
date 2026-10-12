  $ dune exec -- raven --shh ./assignment_field_narrowing.rav
  [Error] File "./assignment_field_narrowing.rav", line 7, columns 2-3:
  7 |   r := x.fraction;
        ^
  Type Error: Expected an expression of type
    Int
  but found an expression of type
    Real.
  [1]
