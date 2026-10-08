  $ dune exec -- raven --shh ./implicit_param_order.rav
  [Error] File "./implicit_param_order.rav", line 2, columns 30-36:
  2 | proc p(implicit ghost x: Int, y: Int)
                                    ^^^^^^
  Syntax Error: Implicit parameters must come last, but the explicit parameter y follows one.
  [1]
