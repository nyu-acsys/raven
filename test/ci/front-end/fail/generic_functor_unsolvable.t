  $ dune exec -- raven --shh ./generic_functor_unsolvable.rav
  [Error] File "./generic_functor_unsolvable.rav", line 11, columns 11-21:
  11 |   var x := M.mk_nil();
                  ^^^^^^^^^^
  Type Error: Cannot infer a type argument for parameter T of M; write an explicit instantiation, e.g. `module M_X = M[...]`.
  [1]
