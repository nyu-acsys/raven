  $ dune exec -- raven --shh tuple_typing1.rav
  [Error] File "tuple_typing1.rav", line 4, columns 7-16:
  4 |   x := (1, 2, 3);
             ^^^^^^^^^
  Type Error: Expected tuple with 2 components.
  [1]

  $ dune exec -- raven --shh tuple_typing2.rav
  [Error] File "tuple_typing2.rav", line 4, columns 11-15:
  4 |   x := (1, true);
                 ^^^^
  Type Error: Expected an expression of type
    Int
  but found an expression of type
    Bool.
  [1]

  $ dune exec -- raven --shh tuple_typing3.rav
  [Error] File "tuple_typing3.rav", line 4, columns 18-20:
  4 |   var y: Bool := x#0;
                        ^^
  Type Error: Expected an expression of type
    Bool
  but found an expression of type
    Int.
  [1]
