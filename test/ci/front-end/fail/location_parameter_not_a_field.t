  $ dune exec -- raven --shh ./location_parameter_not_a_field.rav
  [Error] File "./location_parameter_not_a_field.rav", line 6, columns 11-12:
  6 |   proc p(x.g) { }
                 ^
  Type Error: Expected a field in the location parameter of p, but found function M.g.
  [1]
