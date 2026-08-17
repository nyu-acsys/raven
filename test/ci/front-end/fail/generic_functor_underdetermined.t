  $ dune exec -- raven --shh ./generic_functor_underdetermined.rav
  [Error] File "./generic_functor_underdetermined.rav", line 8, columns 11-20:
  8 |   var x := M.c({||});
                 ^^^^^^^^^
  Type Error: Cannot infer a type argument for parameter T of M; write an explicit instantiation, e.g. `module M_X = M[...]`.
  [1]
