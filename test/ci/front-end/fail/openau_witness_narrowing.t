  $ dune exec -- raven --shh ./openau_witness_narrowing.rav
  [Error] File "./openau_witness_narrowing.rav", line 7, columns 2-9:
  7 |   integer := openAU(token);
        ^^^^^^^
  Type Error: Expected an expression of type
    Map[Int, Int]
  but found an expression of type
    Map[Int, Real].
  [1]
