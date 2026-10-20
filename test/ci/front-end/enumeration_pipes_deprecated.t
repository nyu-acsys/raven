  $ dune exec -- raven --shh ./enumeration_pipes_deprecated.rav
  [Warning] File "./enumeration_pipes_deprecated.rav", line 4, columns 11-13:
  4 |     assert {|1, 2|} == {2, 1}
                 ^^
  Deprecated syntax: write { ... } instead of {| ... |}
  [Warning] File "./enumeration_pipes_deprecated.rav", line 5, columns 11-13:
  5 |     assert [||] ++ [|3|] == [3]
                 ^^
  Deprecated syntax: write [ ... ] instead of [| ... |]
  [Warning] File "./enumeration_pipes_deprecated.rav", line 5, columns 19-21:
  5 |     assert [||] ++ [|3|] == [3]
                         ^^
  Deprecated syntax: write [ ... ] instead of [| ... |]
  [Warning] File "./enumeration_pipes_deprecated.rav", line 6, columns 11-13:
  6 |     assert {|x: Int :: x == 1|} == {1}
                 ^^
  Deprecated syntax: write { ... } instead of {| ... |}
  Verification successful.
