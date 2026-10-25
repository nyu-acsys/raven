  $ dune exec -- raven --shh --typeonly ./applicative_name_collision.rav
  [Error] File "./applicative_name_collision.rav", line 12, columns 72-73:
  12 | func distinct_type_arguments(x: NestedType.T) returns (r: FlatType.T) { x }
                                                                               ^
  Type Error: Expected an expression of type
    Box[(A_B, Anchor)]
  but found an expression of type
    Box[(A.B, Anchor)].
  [Error] File "./applicative_name_collision.rav", line 24, columns 72-73:
  24 | func distinct_functors(x: NestedFunctor.T) returns (r: FlatFunctor.T) { x }
                                                                               ^
  Type Error: Expected an expression of type
    Namespace_Factory[Int]
  but found an expression of type
    Namespace.Factory[Int].
  [1]
