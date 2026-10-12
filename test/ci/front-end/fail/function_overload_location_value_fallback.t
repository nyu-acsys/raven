  $ dune exec -- raven --shh ./function_overload_location_value_fallback.rav
  [Error] File "./function_overload_location_value_fallback.rav", line 9, columns 18-35:
  9 |   var bad: Int := choose(x.slot, 1);
                        ^^^^^^^^^^^^^^^^^
  Type Error: No applicable overload of choose.
  [1]
