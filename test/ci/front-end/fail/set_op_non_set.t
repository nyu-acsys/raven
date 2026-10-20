  $ dune exec -- raven --shh ./set_op_non_set.rav
  [Error] File "./set_op_non_set.rav", line 3, columns 10-18:
  3 |   ensures x ++ {1} == {1}
                ^^^^^^^^
  Type Error: No applicable overload of ++.
  [1]
