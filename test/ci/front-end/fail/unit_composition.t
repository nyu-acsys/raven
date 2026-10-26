  $ dune exec -- raven --shh --typeonly ./unit_composition_field.rav
  [Error] File "./unit_composition_field.rav", line 2, columns 39-44:
  2 | module Outer[E: Library.Type] { module Value = Fresh() }
                                             ^^^^^
  Type Error: A unit factory cannot be applied inside a named-parameter functor when its result introduces a fresh field (Outer.Value.value).
  [1]

  $ dune exec -- raven --shh --typeonly ./unit_composition_predicate.rav
  [Error] File "./unit_composition_predicate.rav", line 2, columns 39-44:
  2 | module Outer[E: Library.Type] { module Value = Fresh() }
                                             ^^^^^
  Type Error: A unit factory cannot be applied inside a named-parameter functor when its result introduces a fresh predicate (Outer.Value.resource).
  [1]

  $ dune exec -- raven --shh --typeonly ./unit_composition_invariant.rav
  [Error] File "./unit_composition_invariant.rav", line 2, columns 39-44:
  2 | module Outer[E: Library.Type] { module Value = Fresh() }
                                             ^^^^^
  Type Error: A unit factory cannot be applied inside a named-parameter functor when its result introduces a fresh invariant (Outer.Value.shared).
  [1]

  $ dune exec -- raven --shh --typeonly ./unit_composition_atomic.rav
  [Error] File "./unit_composition_atomic.rav", line 2, columns 39-44:
  2 | module Outer[E: Library.Type] { module Value = Fresh() }
                                             ^^^^^
  Type Error: A unit factory cannot be applied inside a named-parameter functor when its result introduces a fresh atomic update procedure (Outer.Value.operation).
  [1]

  $ dune exec -- raven --shh --typeonly ./unit_composition_value.rav
  [Error] File "./unit_composition_value.rav", line 2, columns 39-44:
  2 | module Outer[E: Library.Type] { module Value = Fresh() }
                                             ^^^^^
  Type Error: A unit factory cannot be applied inside a named-parameter functor when its result introduces a fresh unspecified value (Outer.Value.value).
  [1]

  $ dune exec -- raven --shh --typeonly ./unit_composition_function.rav
  [Error] File "./unit_composition_function.rav", line 2, columns 39-44:
  2 | module Outer[E: Library.Type] { module Value = Fresh() }
                                             ^^^^^
  Type Error: A unit factory cannot be applied inside a named-parameter functor when its result introduces a fresh uninterpreted function (Outer.Value.choose).
  [1]

  $ dune exec -- raven --shh --typeonly ./unit_composition_nested.rav
  [Error] File "./unit_composition_nested.rav", line 2, columns 39-44:
  2 | module Outer[E: Library.Type] { module Value = Fresh() }
                                             ^^^^^
  Type Error: A unit factory cannot be applied inside a named-parameter functor when its result introduces a fresh data type (Outer.Value.Inner.T).
  [1]

  $ dune exec -- raven --shh --typeonly ./unit_composition_deferred.rav
  [Error] File "./unit_composition_deferred.rav", line 2, columns 39-44:
  2 | module Outer[E: Library.Type] { module Value = Fresh() }
                                             ^^^^^
  Type Error: A unit factory cannot be applied inside a named-parameter functor when its result introduces a fresh data type (Outer.Value.Later.T).
  [1]

  $ dune exec -- raven --shh --typeonly ./unit_composition_opaque.rav
  [Error] File "./unit_composition_opaque.rav", line 3, columns 39-44:
  3 | module Outer[E: Library.Type] { module Value = Fresh() }
                                             ^^^^^
  Type Error: A unit factory cannot be applied inside a named-parameter functor when its result introduces a fresh abstract type (Outer.Value.T).
  [1]

  $ dune exec -- raven --shh --typeonly ./unit_composition_sealed_binding.rav
  [Error] File "./unit_composition_sealed_binding.rav", line 4, columns 39-44:
  4 | module Outer[E: Library.Type] { module Value = Fresh() }
                                             ^^^^^
  Type Error: A unit factory cannot be applied inside a named-parameter functor when its result introduces a fresh abstract type (Outer.Value.Hidden.T).
  [1]

  $ dune exec -- raven --shh --typeonly ./unit_composition_nested_unit.rav
  [Error] File "./unit_composition_nested_unit.rav", line 3, columns 39-44:
  3 | module Outer[E: Library.Type] { module Value = Fresh() }
                                             ^^^^^
  Type Error: A unit factory cannot be applied inside a named-parameter functor when its result introduces a fresh field (Outer.Value.Value.value).
  [1]

  $ dune exec -- raven --shh --typeonly ./unit_composition_local_argument.rav
  [Error] File "./unit_composition_local_argument.rav", line 7, columns 39-44:
  7 | module Outer[E: Library.Type] { module Value = Fresh() }
                                             ^^^^^
  Type Error: A unit factory cannot be applied inside a named-parameter functor when its result introduces a fresh data type (Generic[Fresh.Local].T).
  [1]

  $ dune exec -- raven --shh --typeonly ./unit_composition_inherited.rav
  [Error] File "./unit_composition_inherited.rav", line 3, columns 39-44:
  3 | module Outer[E: Library.Type] { module Value = Fresh() }
                                             ^^^^^
  Type Error: A unit factory cannot be applied inside a named-parameter functor when its result introduces a fresh field (Outer.Value.value).
  [1]

  $ dune exec -- raven --shh --typeonly ./unit_composition_recursive.rav
  [Error] File "./unit_composition_recursive.rav", line 3, columns 34-40:
  3 | module Outer[F: Factory] { module Result = F() }
                                        ^^^^^^
  Type Error: A unit factory cannot be applied inside a named-parameter functor when its result introduces a fresh recursive module identity (Outer.Result.Value.Next).
  [1]
