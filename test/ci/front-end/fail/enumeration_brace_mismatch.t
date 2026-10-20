  $ dune exec -- raven --shh ./enumeration_brace_mismatch.rav
  [Error] File "./enumeration_brace_mismatch.rav", line 3, columns 18-18:
  3 |     assert {|1, 2} == {1, 2}
                        ^
  Syntax Error: Unexpected token '}'.
  [1]
