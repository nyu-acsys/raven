  $ dune exec -- raven --shh ./function_overload_return_fallback.rav
  [Error] File "./function_overload_return_fallback.rav", line 4, columns 17-21:
  4 |   var x: Real := f(0);
                       ^^^^
  Type Error: Expected an expression of type
    Real
  but found an expression of type
    Bool.
  [1]
