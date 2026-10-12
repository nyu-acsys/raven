  $ dune exec -- raven --shh ./function_overload_ghost_nonformal.rav
  [Error] File "./function_overload_ghost_nonformal.rav", line 6, columns 18-32:
  6 |   var bad: Int := h(ordinary(g));
                        ^^^^^^^^^^^^^^
  Type Error: No applicable overload of h.
  [1]
