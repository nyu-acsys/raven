  $ dune exec -- raven --shh ./enumeration_brace_mismatch.rav
  [Warning] File "./enumeration_brace_mismatch.rav", line 3, columns 11-13:
  3 |     assert {|1, 2} == {1, 2}
                 ^^
  Deprecated syntax: write { ... } instead of {| ... |}
  [Error] File "./enumeration_brace_mismatch.rav", line 3, columns 18-18:
  3 |     assert {|1, 2} == {1, 2}
                        ^
  Syntax Error: Unexpected token '}'.
  [1]
