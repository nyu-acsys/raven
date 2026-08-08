  $ dune exec -- raven --shh ./reach_back_cross_parent.rav
  [Error] File "./reach_back_cross_parent.rav", line 32, columns 6-7:
  32 |   inv i(x: Ref) {
             ^
  Type Error: invariant i implements interface M1's abstract i, but its definition depends on N.test, which M2 declares.
  [1]
