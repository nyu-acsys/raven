  $ dune exec -- raven --shh ./finset_no_downcast.rav
  [Error] File "./finset_no_downcast.rav", line 7, columns 4-5:
  7 |     s
          ^
  Type Error: Expected an expression of type
    FinSet[Int]
  but found an expression of type
    Set[Int].
  [1]
