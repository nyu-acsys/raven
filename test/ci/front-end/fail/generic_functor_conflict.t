  $ dune exec -- raven --shh ./generic_functor_conflict.rav
  [Error] File "./generic_functor_conflict.rav", line 10, columns 11-24:
  10 |   var x := M.mk(3, true);
                  ^^^^^^^^^^^^^
  Type Error: Cannot infer a single type for parameter T of M: found both Int and Bool.
  [1]
