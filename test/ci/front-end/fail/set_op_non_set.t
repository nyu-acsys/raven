  $ dune exec -- raven --shh ./set_op_non_set.rav
  [Error] File "./set_op_non_set.rav", line 3, columns 10-11:
  3 |   ensures x ++ {|1|} == {|1|}
                ^
  Type Error: Expected an expression of type
    Set[Bot]
  but found an expression of type
    Int.
  [1]
