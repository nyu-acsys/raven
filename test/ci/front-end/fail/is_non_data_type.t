  $ dune exec -- raven --shh ./is_non_data_type.rav
  [Error] File "./is_non_data_type.rav", line 3, columns 11-20:
  3 |   requires x is cons
                 ^^^^^^^^^
  Type Error: 'is' can only test the constructor of a value of a `data` type.
  [1]
