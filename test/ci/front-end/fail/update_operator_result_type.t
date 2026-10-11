  $ dune exec -- raven --shh ./update_operator_result_type.rav
  [Error] File "./update_operator_result_type.rav", line 1, columns 5-12:
  1 | func _[_:=_](s: Int, i: Int, e: Int) returns (r: Bool) { true }
           ^^^^^^^
  Type Error: An update operator must return the same type as its container parameter.
  [1]
