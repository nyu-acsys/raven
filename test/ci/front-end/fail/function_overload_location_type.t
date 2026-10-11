  $ dune exec -- raven --shh ./function_overload_location_type.rav
  [Error] File "./function_overload_location_type.rav", line 8, columns 18-35:
  8 |   var bad: Int := Ops.tag(x.bit, 9);
                        ^^^^^^^^^^^^^^^^^
  Type Error: No applicable overload of Ops.tag.
  [1]
