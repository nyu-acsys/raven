  $ dune exec -- raven --shh ./function_overload_duplicate.rav
  [Error] File "./function_overload_duplicate.rav", line 3, columns 5-6:
  3 | func f(y: Int) returns (r: Bool) { true }
           ^
  Error: Identifier f has already been declared in this scope.
  [1]
