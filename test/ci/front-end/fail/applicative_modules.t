  $ dune exec -- raven --shh ./applicative_same_rep.rav
  [Error] File "./applicative_same_rep.rav", line 8, columns 43-44:
  8 | func cannot_mix(x: A.T) returns (r: B.T) { x }
                                                 ^
  Type Error: Expected an expression of type
    Box[SecondArgument]
  but found an expression of type
    Box[FirstArgument].
  [1]

  $ dune exec -- raven --shh ./applicative_fresh_arguments.rav
  [Error] File "./applicative_fresh_arguments.rav", line 9, columns 43-44:
  9 | func cannot_mix(x: A.T) returns (r: B.T) { x }
                                                 ^
  Type Error: Expected an expression of type
    Box[SecondArgument]
  but found an expression of type
    Box[FirstArgument].
  [1]

  $ dune exec -- raven --shh ./applicative_fresh_outer.rav
  [Error] File "./applicative_fresh_outer.rav", line 10, columns 43-44:
  10 | func cannot_mix(x: A.T) returns (r: B.T) { x }
                                                  ^
  Type Error: Expected an expression of type
    SecondOuter.Inner[Int]
  but found an expression of type
    FirstOuter.Inner[Int].
  [1]

  $ dune exec -- raven --shh ./applicative_opaque_views.rav
  [Error] File "./applicative_opaque_views.rav", line 7, columns 43-44:
  7 | func cannot_mix(x: A.T) returns (r: B.T) { x }
                                                 ^
  Type Error: Expected an expression of type
    B.T
  but found an expression of type
    A.T.
  [1]

  $ dune exec -- raven --shh ./applicative_hidden_member.rav
  [Error] File "./applicative_hidden_member.rav", line 7, columns 13-16:
  7 |   val x := A.box(0);
                   ^^^
  Error: box is not accessible here: A is sealed with interface View and exposes only its members.
  [1]

  $ dune exec -- raven --shh ./applicative_argument_contract.rav
  [Error] File "./applicative_argument_contract.rav", line 6, columns 18-26:
  6 | module Bad = Uses[Argument]
                        ^^^^^^^^
  Type Error: Module Argument does not implement interface Required.
  [1]

  $ dune exec -- raven --shh ./applicative_fresh_results.rav
  [Error] File "./applicative_fresh_results.rav", line 6, columns 43-44:
  6 | func cannot_mix(x: A.T) returns (r: B.T) { x }
                                                 ^
  Type Error: Expected an expression of type
    B.T
  but found an expression of type
    A.T.
  [1]

  $ dune exec -- raven --shh ./applicative_overloads.rav
  [Error] File "./applicative_overloads.rav", line 18, columns 9-15:
  18 |   assert get(b);
                ^^^^^^
  Type Error: Ambiguous function name get (2 candidates); add a type annotation or qualify the call.
  [1]
