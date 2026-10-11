  $ dune exec -- raven --shh --nostdlib ./operator_mixfix_callable_kind.rav
  [Error] File "./operator_mixfix_callable_kind.rav", line 1, columns 5-11:
  1 | proc _[_..](s: Int, lo: Int) returns (r: Int) { r := s + lo; }
           ^^^^^^
  Type Error: A mixfix operator must be declared as a function.
  [1]
