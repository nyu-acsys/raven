  $ dune exec -- raven --shh ./unfold_witness_narrowing.rav
  [Error] File "./unfold_witness_narrowing.rav", line 9, columns 20-27:
  9 |   unfold real_map()[integer := witness];
                          ^^^^^^^
  Type Error: Expected an expression of type
    Map[Int, Int]
  but found an expression of type
    Map[Int, Real].
  [1]
