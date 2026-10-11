  $ dune exec -- raven --shh ./function_overload_ambiguous.rav
  [Error] File "./function_overload_ambiguous.rav", line 13, columns 16-20:
  13 |   var x: Int := f(0);
                       ^^^^
  Type Error: Ambiguous function name f (2 candidates); add a type annotation or qualify the call.
  [1]
