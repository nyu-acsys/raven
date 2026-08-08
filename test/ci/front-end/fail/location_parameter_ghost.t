  $ dune exec -- raven --shh ./location_parameter_ghost.rav
  [Error] File "./location_parameter_ghost.rav", line 5, columns 9-20:
  5 |   proc p(ghost x.A.f) { }
               ^^^^^^^^^^^
  Syntax Error: A location parameter such as 'x.f' cannot be ghost or implicit.
  [1]
