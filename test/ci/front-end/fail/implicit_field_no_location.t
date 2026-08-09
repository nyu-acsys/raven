  $ dune exec -- raven --shh ./implicit_field_no_location.rav
  [Error] File "./implicit_field_no_location.rav", line 22, columns 13-14:
  22 |   { p := get(x); }
                    ^
  Type Error: Cannot infer the field argument for parameter A of Ops from this argument; pass a location, `x.f`, or write an explicit instantiation, e.g. `module M_X = Ops[...]`.
  [1]
