  $ dune exec -- raven --shh --extension auto ./auto_mixed.rav
  [Error] File "./auto_mixed.rav", line 5, columns 13-26:
  5 |     requires EC.error(0.5)
                   ^^^^^^^^^^^^^
  Error: this expression belongs to the eris extension, but this file also uses a type belonging to the default extension; --extension auto cannot pick a single mode for it, re-run with an explicit --extension flag.
  [Error] File "./auto_mixed.rav", line 2, columns 11-25:
  2 |   field p: Proph[Bool, 1]
                 ^^^^^^^^^^^^^^
  Related Location: this type belongs to the default extension.
  [1]
