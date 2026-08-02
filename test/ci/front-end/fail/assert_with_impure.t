  $ dune exec -- raven --shh ./assert_with_impure.rav
  [Error] File "./assert_with_impure.rav", line 16, columns 9-13:
  16 |   assert p(x) with {
                ^^^^
  Type Error: Expected an expression of type
    Bool
  but found an expression of type
    Perm.
  [1]
