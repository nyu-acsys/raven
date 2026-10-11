  $ dune exec -- raven --shh ./function_overload_no_match.rav
  [Error] File "./function_overload_no_match.rav", line 4, columns 17-24:
  4 |   var x: Bool := f(true);
                       ^^^^^^^
  Type Error: No applicable overload of f.
  [1]
