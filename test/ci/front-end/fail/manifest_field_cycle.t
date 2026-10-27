  $ dune exec -- raven --shh ./manifest_field_cycle.rav
  [Error] File "./manifest_field_cycle.rav", line 6, columns 23-24:
  6 | module A { field f = B.g }
                             ^
  Error: Unknown identifier B.g.
  [Error] File "./manifest_field_cycle.rav", line 7, columns 23-24:
  7 | module B { field g = A.f }
                             ^
  Error: Unknown identifier A.f.
  [1]
