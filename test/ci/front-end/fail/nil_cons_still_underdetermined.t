  $ dune exec -- raven --shh ./nil_cons_still_underdetermined.rav
  [Error] File "./nil_cons_still_underdetermined.rav", line 11, columns 9-19:
  11 |   assert nil :: nil == nil :: nil;
                ^^^^^^^^^^
  Type Error: Cannot infer a type argument for parameter E of Library.List; write an explicit instantiation, e.g. `module M_X = Library.List[...]`.
  [1]
