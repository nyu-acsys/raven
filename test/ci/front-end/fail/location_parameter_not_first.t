  $ dune exec -- raven --shh ./location_parameter_not_first.rav
  [Error] File "./location_parameter_not_first.rav", line 4, columns 9-29:
  4 |   proc p(x.A.f, n: Int, y.B.f) { }
               ^^^^^^^^^^^^^^^^^^^^
  Syntax Error: Location parameters such as 'x.f' must come before ordinary ones.
  [1]
