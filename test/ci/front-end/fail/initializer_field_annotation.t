  $ dune exec -- raven --shh ./initializer_field_annotation.rav
  [Error] File "./initializer_field_annotation.rav", line 6, columns 6-11:
  6 |   var value: Bool := x.integer;
            ^^^^^
  Type Error: Expected an expression of type
    Bool
  but found an expression of type
    Int.
  [1]
