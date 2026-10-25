  $ dune exec -- raven --shh ./resource_alias_function.rav
  [Error] File "./resource_alias_function.rav", line 2, columns 18-26:
  2 | module Bad { func identity(x: Int) returns (r: Int) = identity }
                        ^^^^^^^^
  Type Error: Only predicates and invariants may be resource aliases.
  [1]
