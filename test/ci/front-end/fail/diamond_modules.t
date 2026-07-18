  $ dune exec -- raven --shh ./diamond_modules.rav
  [Error] File "./diamond_modules.rav", line 23, columns 10-11:
  23 |     B1.p1(x);
                 ^
  Type Error: Expected an expression of type
    D.B1.A1.T
  but found an expression of type
    D.A2.T.
  
  D.B1.A1.T and D.A2.T are two different names for the same module (A). Raven does not currently recognize their members as the same type -- use one name consistently wherever this type must match.
  [1]
