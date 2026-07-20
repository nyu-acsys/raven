  $ dune exec -- raven --shh ./bad_domain.rav
  [Error] File "./bad_domain.rav", line 2, columns 12-13:
  2 |   decreases b
                  ^
  Type Error: Expected an expression of type
    Int
  but found an expression of type
    Bool.
  [1]
