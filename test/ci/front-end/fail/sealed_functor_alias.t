  $ dune exec -- raven --shh --typeonly ./sealed_functor_alias_representation.rav
  [Error] File "./sealed_functor_alias_representation.rav", line 9, columns 40-41:
  9 | func bad(x: First.T) returns (r: Int) { x }
                                              ^
  Type Error: Expected an expression of type
    Int
  but found an expression of type
    Hidden[Int].T.
  [1]

  $ dune exec -- raven --shh --typeonly ./sealed_functor_alias_implementation.rav
  [Error] File "./sealed_functor_alias_implementation.rav", line 10, columns 47-48:
  10 | func bad(x: First.T) returns (r: Concrete.T) { x }
                                                      ^
  Type Error: Expected an expression of type
    Int
  but found an expression of type
    Hidden[Int].T.
  [1]

  $ dune exec -- raven --shh --typeonly ./sealed_functor_alias_views.rav
  [Error] File "./sealed_functor_alias_views.rav", line 11, columns 45-46:
  11 | func bad(x: First.T) returns (r: Second.T) { x }
                                                    ^
  Type Error: Expected an expression of type
    Other[Int].T
  but found an expression of type
    Hidden[Int].T.
  [1]

  $ dune exec -- raven --shh --typeonly ./sealed_functor_alias_arguments.rav
  [Error] File "./sealed_functor_alias_arguments.rav", line 10, columns 45-46:
  10 | func bad(x: First.T) returns (r: Second.T) { x }
                                                    ^
  Type Error: Expected an expression of type
    Hidden[Bool].T
  but found an expression of type
    Hidden[Int].T.
  [1]

  $ dune exec -- raven --shh --typeonly ./sealed_functor_alias_extra.rav
  [Error] File "./sealed_functor_alias_extra.rav", line 9, columns 27-32:
  9 | lemma bad() { assert First.extra() == 1; }
                                 ^^^^^
  Error: Unknown identifier First.extra.
  [1]

  $ dune exec -- raven --shh --typeonly ./sealed_functor_alias_unapplied.rav
  [Error] File "./sealed_functor_alias_unapplied.rav", line 9, columns 19-20:
  9 | func bad(x: Hidden.T) returns (r: Bool) { true }
                         ^
  Error: T is not accessible here: Hidden is a sealed module, which exposes only the members of interface Signature.
  [1]

  $ dune exec -- raven --shh --typeonly ./sealed_functor_alias_arity.rav
  [Error] File "./sealed_functor_alias_arity.rav", line 9, columns 13-19:
  9 | module Bad = Hidden[Int, Bool]
                   ^^^^^^
  Type Error: Module Hidden expects one argument.
  [1]

  $ dune exec -- raven --shh --typeonly ./sealed_functor_alias_unit.rav
  [Error] File "./sealed_functor_alias_unit.rav", line 7, columns 36-37:
  7 | func bad(x: A.T) returns (r: B.T) { x }
                                          ^
  Type Error: Expected an expression of type
    B.T
  but found an expression of type
    A.T.
  [1]

  $ dune exec -- raven --shh --typeonly ./sealed_functor_alias_nominal.rav
  [Error] File "./sealed_functor_alias_nominal.rav", line 3, columns 7-13:
  3 | module Hidden :> Signature = Implementation
             ^^^^^^
  Type Error: Module Implementation does not implement interface Signature.
  [1]
