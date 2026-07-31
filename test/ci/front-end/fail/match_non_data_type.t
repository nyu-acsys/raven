  $ dune exec -- raven --shh ./match_non_data_type.rav
  [Error] File "./match_non_data_type.rav", line 3, columns 7-32:
  3 |   r := match x { case nil => 0 };
             ^^^^^^^^^^^^^^^^^^^^^^^^^
  Type Error: a `match` scrutinee must have a `data` type.
  [1]
