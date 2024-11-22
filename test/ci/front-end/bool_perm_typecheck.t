  $ dune exec -- raven --shh ./bool_perm_typecheck.rav
  [Error] File "./bool_perm_typecheck.rav", line 8, columns 9-30:
  8 |   inhale own(x.f, 1, 1.0) && b ? true : false;
               ^^^^^^^^^^^^^^^^^^^^^
  Type Error: Expected an expression of type
    Bool
  but found an expression of type
    Perm.
  [1]
