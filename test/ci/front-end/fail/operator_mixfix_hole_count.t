  $ dune exec -- raven --shh --nostdlib ./operator_mixfix_hole_count.rav
  [Error] File "./operator_mixfix_hole_count.rav", line 1, columns 5-12:
  1 | func _[_.._](s: Int, hi: Int) returns (r: Int) { s + hi }
           ^^^^^^^
  Type Error: Mixfix operator _[_.._] requires 3 explicit parameters, followed only by implicit ghost parameters.
  [1]
