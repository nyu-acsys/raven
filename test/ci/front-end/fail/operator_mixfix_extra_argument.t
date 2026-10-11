  $ dune exec -- raven --shh --nostdlib ./operator_mixfix_extra_argument.rav
  [Error] File "./operator_mixfix_extra_argument.rav", line 1, columns 5-11:
  1 | func _[.._](s: Int, hi: Int, extra: Int) returns (r: Int) { s + hi + extra }
           ^^^^^^
  Type Error: Mixfix operator _[.._] requires 2 explicit parameters, followed only by implicit ghost parameters.
  [1]
