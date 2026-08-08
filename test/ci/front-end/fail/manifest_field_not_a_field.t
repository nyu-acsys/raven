  $ dune exec -- raven --shh ./manifest_field_not_a_field.rav
  [Error] File "./manifest_field_not_a_field.rav", line 6, columns 12-13:
  6 |   field f = g
                  ^
  Type Error: Expected a field on the right-hand side of 'field f = ...', but found function M.g.
  [1]
