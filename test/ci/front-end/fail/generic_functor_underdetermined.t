  $ dune exec -- raven --shh ./generic_functor_underdetermined.rav
  [Error] File "./generic_functor_underdetermined.rav", line 8, columns 15-19:
  8 |   var x := M.c({||});
                     ^^^^
  Type Error: Cannot infer a type argument for M from this argument: the type of `{||}` cannot be uniquely determined here. Give it an explicit type annotation, or write an explicit instantiation, e.g. `module M_X = M[...]`.
  [1]
