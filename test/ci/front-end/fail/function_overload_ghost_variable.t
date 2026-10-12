  $ dune exec -- raven --shh ./function_overload_ghost_variable.rav
  [Error] File "./function_overload_ghost_variable.rav", line 5, columns 18-22:
  5 |   var bad: Int := h(g);
                        ^^^^
  Type Error: No applicable overload of h.
  [1]
