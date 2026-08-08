  $ dune exec -- raven --shh ./location_argument_wrong_field.rav
  [Error] File "./location_argument_wrong_field.rav", line 19, columns 16-23:
  19 |   { r := O.read(x.other, v); }
                       ^^^^^^^
  Type Error: read operates on field HF.f here, but this argument names other.
  [1]
