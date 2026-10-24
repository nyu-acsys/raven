  $ dune exec -- raven --shh --typeonly ./generic_instance_placement_nominal.rav
  [Error] File "./generic_instance_placement_nominal.rav", line 10, columns 32-52:
  10 |   val wrong: Pair[Int, Bool] := GenericNamed.make(1);
                                       ^^^^^^^^^^^^^^^^^^^^
  Type Error: Expected an expression of type
    Pair[Int, Bool]
  but found an expression of type
    Pair[NamedInt, Bool].
  [1]
