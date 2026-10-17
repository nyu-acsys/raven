  $ dune exec -- raven --shh --extension eris ./lazy_coin.rav
  [Error] File "./lazy_coin.rav", line 5, columns 11-25:
  5 |   field p: Proph[Bool, 1]
                 ^^^^^^^^^^^^^^
  Error: this type belongs to the default extension; re-run with --extension default.
  [Error] File "./lazy_coin.rav", line 12, columns 12-26:
  12 |     var p1: Proph[Bool, 1];
                   ^^^^^^^^^^^^^^
  Error: this type belongs to the default extension; re-run with --extension default.
  [Error] File "./lazy_coin.rav", line 44, columns 41-55:
  44 |     exists b': Library.Option[Bool], p': Proph[Bool, 1] ::
                                                ^^^^^^^^^^^^^^
  Error: this type belongs to the default extension; re-run with --extension default.
  [1]
