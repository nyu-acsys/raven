  $ dune exec -- raven --shh ./assert_with_non_assert.rav
  [Error] File "./assert_with_non_assert.rav", line 6, columns 2-2:
  6 |   assume true with {
        ^
  Syntax Error: A 'with' clause is only allowed in assert statements.
  [1]
