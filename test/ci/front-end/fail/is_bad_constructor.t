  $ dune exec -- raven --shh ./is_bad_constructor.rav
  [Error] File "./is_bad_constructor.rav", line 8, columns 11-21:
  8 |   requires x is bogus
                 ^^^^^^^^^^
  Type Error: 'bogus' is not a constructor of this data type.
  [1]
