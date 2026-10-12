  $ dune exec -- raven --shh ./function_overload_wrong_location_field.rav
  [Error] File "./function_overload_wrong_location_field.rav", line 8, columns 18-30:
  8 |   var bad: Ref := key(x.other);
                        ^^^^^^^^^^^^
  Type Error: No applicable overload of key.
  [1]
