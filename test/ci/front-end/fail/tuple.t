  $ dune exec -- raven --shh ./tuple.rav
  [Error] File "./tuple.rav", line 7, columns 20-22:
  7 |     var zz: Int := x#2;
                          ^^
  Type Error: Tuple index 2 is out of bounds; (Int, Bool) has 2 component(s).
  [1]
