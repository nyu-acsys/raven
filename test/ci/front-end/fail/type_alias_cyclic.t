  $ dune exec -- raven --shh ./type_alias_cyclic_self.rav
  [Error] File "./type_alias_cyclic_self.rav", line 3, columns 7-8:
  3 |   type K = K
             ^
  Type Error: The definition of type K refers to itself. Only data types can be recursive.
  [1]
  $ dune exec -- raven --shh ./type_alias_cyclic_mutual.rav
  [Error] File "./type_alias_cyclic_mutual.rav", line 4, columns 7-8:
  4 |   type B = A
             ^
  Type Error: The definition of type B refers to itself. Only data types can be recursive.
  [1]
  $ dune exec -- raven --shh ./type_alias_cyclic_nested.rav
  [Error] File "./type_alias_cyclic_nested.rav", line 4, columns 7-8:
  4 |   type A = Map[Int, A]
             ^
  Type Error: The definition of type A refers to itself. Only data types can be recursive.
  [1]
