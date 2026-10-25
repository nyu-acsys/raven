  $ dune exec -- raven --shh ./unit_factories.rav
  [Error] File "./unit_factories.rav", line 8, columns 7-8:
  8 |   r := x;
             ^
  Type Error: Expected an expression of type
    B.T
  but found an expression of type
    A.T.
  [1]

  $ dune exec -- raven --shh ./unit_factory_named_call.rav
  [Error] File "./unit_factory_named_call.rav", line 2, columns 7-10:
  2 | module Bad = Named()
             ^^^
  Type Error: Only a unit factory can be applied with ().
  [1]

  $ dune exec -- raven --shh ./unit_factory_named_argument.rav
  [Error] File "./unit_factory_named_argument.rav", line 2, columns 7-10:
  2 | module Bad = Fresh[Int]
             ^^^
  Type Error: A unit factory must be applied with ().
  [1]

  $ dune exec -- raven --shh ./unit_factory_structure_call.rav
  [Error] File "./unit_factory_structure_call.rav", line 2, columns 7-10:
  2 | module Bad = Plain()
             ^^^
  Type Error: Only a unit factory can be applied with ().
  [1]

  $ dune exec -- raven --shh ./unit_factory_unapplied.rav
  [Error] File "./unit_factory_unapplied.rav", line 4, columns 18-19:
  4 | proc bad(x: Fresh.T) { }
                        ^
  Error: Unknown identifier Fresh.T.
  [1]

  $ dune exec -- raven --shh ./unit_factory_inside_named.rav
  [Error] File "./unit_factory_inside_named.rav", line 5, columns 9-12:
  5 |   module Bad = Fresh()
               ^^^
  Type Error: A unit factory cannot be applied inside a named-parameter functor.
  [1]

  $ dune exec -- raven --shh ./unit_factory_alias_inside_named.rav
  [Error] File "./unit_factory_alias_inside_named.rav", line 6, columns 9-12:
  6 |   module Bad = Alias()
               ^^^
  Type Error: A unit factory cannot be applied inside a named-parameter functor.
  [1]

  $ dune exec -- raven --shh ./unit_factory_formal_inside_named.rav
  [Error] File "./unit_factory_formal_inside_named.rav", line 5, columns 9-12:
  5 |   module Bad = F()
               ^^^
  Type Error: A unit factory cannot be applied inside a named-parameter functor.
  [1]

  $ dune exec -- raven --shh ./unit_factory_unused_body.rav
  [Error] File "./unit_factory_unused_body.rav", line 6, columns 3-3:
  6 |   }
         ^
  Verification Error: A postcondition may not hold at this return point.
  [Error] File "./unit_factory_unused_body.rav", line 3, columns 12-18:
  3 |     ensures r == 0
                  ^^^^^^
  Related Location: This assertion may not hold.
  [1]

  $ dune exec -- raven --shh ./unit_factory_higher_order_shape.rav
  [Error] File "./unit_factory_higher_order_shape.rav", line 8, columns 18-23:
  8 | module Bad = Uses[Named]
                        ^^^^^
  Type Error: Module Named does not implement interface Factory.
  [1]

  $ dune exec -- raven --shh ./unit_factory_result_shape.rav
  [Error] File "./unit_factory_result_shape.rav", line 8, columns 18-23:
  8 | module Bad = Uses[Fresh]
                        ^^^^^
  Type Error: Module Fresh first needs to be instantiated to obtain a module with interface Result.
  [1]

  $ dune exec -- raven --shh ./unit_factory_nested_unapplied.rav
  [Error] File "./unit_factory_nested_unapplied.rav", line 7, columns 26-27:
  7 | proc bad(x: Applied.Fresh.T) { }
                                ^
  Error: Unknown identifier Applied.Fresh.T.
  [1]

  $ dune exec -- raven --shh ./unit_factory_applied_argument.rav
  [Error] File "./unit_factory_applied_argument.rav", line 9, columns 18-19:
  9 | module Bad = Uses[A]
                        ^
  Type Error: The module does not have its interface's parameter shape.
  [1]

  $ dune exec -- raven --shh ./unit_factory_alias_unapplied.rav
  [Error] File "./unit_factory_alias_unapplied.rav", line 5, columns 18-19:
  5 | proc bad(x: Alias.T) { }
                        ^
  Error: Unknown identifier Alias.T.
  [1]

  $ dune exec -- raven --shh ./unit_factory_mixed_parents.rav
  [Error] File "./unit_factory_mixed_parents.rav", line 3, columns 7-12:
  3 | module Mixed() : UnitParent, NamedParent {
             ^^^^^
  Type Error: The interfaces impose incompatible module parameter shapes.
  [1]

  $ dune exec -- raven --shh ./unit_factory_formal_unapplied.rav
  [Error] File "./unit_factory_formal_unapplied.rav", line 3, columns 31-32:
  3 |   proc cannot_read_result(x: F.T) { }
                                     ^
  Error: Unknown identifier F.T.
  [1]

  $ dune exec -- raven --shh ./unit_factory_sealed_alias.rav
  [Error] File "./unit_factory_sealed_alias.rav", line 3, columns 7-13:
  3 | module Hidden :> Factory = Fresh
             ^^^^^^
  Type Error: Seal the functor declaration or its applied result instead of an unapplied alias.
  [1]

  $ dune exec -- raven --shh ./unit_factory_bare_type.rav
  [Error] File "./unit_factory_bare_type.rav", line 4, columns 12-17:
  4 | proc bad(x: Fresh) { }
                  ^^^^^
  Type Error: A unit factory must be applied with () before using its result type.
  [1]

  $ dune exec -- raven --shh ./unit_factory_sealed_result.rav
  [Error] File "./unit_factory_sealed_result.rav", line 5, columns 42-47:
  5 | proc cannot_construct() { val x := Hidden.token; }
                                                ^^^^^
  Error: token is not accessible here: Hidden is sealed with interface Factory and exposes only its members.
  [1]

  $ dune exec -- raven --shh ./unit_factory_fresh_outer.rav
  [Error] File "./unit_factory_fresh_outer.rav", line 5, columns 60-61:
  5 | proc cannot_mix(x: A.Value.T) returns (r: B.Value.T) { r := x; }
                                                                  ^
  Type Error: Expected an expression of type
    B.Value.T
  but found an expression of type
    A.Value.T.
  [1]

  $ dune exec -- raven --shh ./unit_factory_sealed_views.rav
  [Error] File "./unit_factory_sealed_views.rav", line 6, columns 61-62:
  6 | proc cannot_mix_views(x: Left.T) returns (r: Right.T) { r := x; }
                                                                   ^
  Type Error: Expected an expression of type
    Right.T
  but found an expression of type
    Left.T.
  [1]

  $ dune exec -- raven --shh ./unit_factory_opaque_member.rav
  [Error] File "./unit_factory_opaque_member.rav", line 8, columns 58-59:
  8 | proc cannot_mix(x: A.Leaf.T) returns (r: B.Leaf.T) { r := x; }
                                                                ^
  Type Error: Expected an expression of type
    B.Leaf.T
  but found an expression of type
    A.Leaf.T.
  [1]

  $ dune exec -- raven --shh ./unit_factory_member_result.rav
  [Error] File "./unit_factory_member_result.rav", line 5, columns 33-37:
  5 | module Bad : HasFactory { module Make = Value }
                                       ^^^^
  Type Error: The module member does not preserve its interface's parameter shape.
  [1]
