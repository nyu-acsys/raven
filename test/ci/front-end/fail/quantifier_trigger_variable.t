  $ dune exec -- raven --shh ./quantifier_trigger_variable.rav
  [Error] File "./quantifier_trigger_variable.rav", line 5, columns 36-40:
  5 |   ensures forall x: Int, y: Int :: {f(x)} f(x) == f(x) + y - y
                                          ^^^^
  Type Error: This trigger does not mention the variable y.
  [1]
