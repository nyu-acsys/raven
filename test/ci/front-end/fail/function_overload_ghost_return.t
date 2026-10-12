  $ dune exec -- raven --shh ./function_overload_ghost_return.rav
  [Error] File "./function_overload_ghost_return.rav", line 6, columns 18-35:
  6 |   var bad: Int := h(ghost_result());
                        ^^^^^^^^^^^^^^^^^
  Type Error: No applicable overload of h.
  [1]
