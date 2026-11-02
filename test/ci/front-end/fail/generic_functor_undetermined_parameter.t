  $ dune exec -- raven --shh ./generic_functor_undetermined_parameter.rav
  [Error] File "./generic_functor_undetermined_parameter.rav", line 15, columns 11-21:
  15 |   var x := Pair.mk(3);
                  ^^^^^^^^^^
  Type Error: Cannot infer parameter S of Pair: its interface declares neither a rep type nor a single field, so no call determines it; write an explicit instantiation, e.g. `module M_X = Pair[...]`.
  [1]
