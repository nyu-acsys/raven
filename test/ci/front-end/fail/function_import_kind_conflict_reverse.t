  $ dune exec -- raven --shh ./function_import_kind_conflict_reverse.rav
  [Error] File "./function_import_kind_conflict_reverse.rav", line 11, columns 2-12:
  11 |   import A._
         ^^^^^^^^^^
  Error: Identifier f has already been declared in this scope.
  [1]
