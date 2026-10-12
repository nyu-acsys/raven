  $ dune exec -- raven --shh ./bind_non_assertion.rav
  [Error] File "./bind_non_assertion.rav", line 3, columns 7-8:
  3 |   x :| 3;
             ^
  Type Error: Expected an expression of type
    Perm
  but found an expression of type
    Int.
  [1]
