  $ dune exec -- raven --shh ./redeclared_type.rav
  [Error] File "./redeclared_type.rav", line 4, columns 2-8:
  4 |   type K = K
        ^^^^^^
  Error: Identifier K has already been declared in this scope.
  [1]
  $ dune exec -- raven --shh ./redeclared_field.rav
  [Error] File "./redeclared_field.rav", line 5, columns 2-14:
  5 |   field f: Int
        ^^^^^^^^^^^^
  Error: Identifier f has already been declared in this scope.
  [1]
