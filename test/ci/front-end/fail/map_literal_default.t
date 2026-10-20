  $ dune exec -- raven --shh ./map_literal_default.rav
  [Error] File "./map_literal_default.rav", line 3, columns 20-20:
  3 |     var m := {1 := 5}
                          ^
  Syntax Error: A map literal needs a value for the other keys: add `else e`.
  [1]
