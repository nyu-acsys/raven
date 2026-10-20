  $ dune exec -- raven --shh ./function_overload_crossed.rav
  [Error] File "./function_overload_crossed.rav", line 4, columns 16-31:
  4 |   var x: Int := f({ 1 }, { 2 });
                      ^^^^^^^^^^^^^^^
  Type Error: Ambiguous function name f (2 candidates); add a type annotation or qualify the call.
  [1]
