  $ dune exec -- raven --shh hidden_import.rav
  [Warning] File "hidden_import.rav", line 11, columns 2-12:
  11 |   import A.f
         ^^^^^^^^^^
  This import of A.f is hidden by the declaration of f on line 14
  [Warning] File "hidden_import.rav", line 18, columns 2-12:
  18 |   import A.h
         ^^^^^^^^^^
  This import of A.h is hidden by the declaration of h on line 16
  Verification successful.
