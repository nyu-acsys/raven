  $ dune exec -- raven --shh ./generic_functor_no_rep_interface.rav
  [Error] File "./generic_functor_no_rep_interface.rav", line 13, columns 11-18:
  13 |   var x := P.id(3);
                  ^^^^^^^
  Type Error: Cannot infer parameter X of P: its interface declares neither a rep type nor a single field, so no call determines it; write an explicit instantiation, e.g. `module M_X = P[...]`.
  [1]
