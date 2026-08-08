  $ dune exec -- raven --shh ./reach_back_parameterized_parent.rav
  [Error] File "./reach_back_parameterized_parent.rav", line 40, columns 6-7:
  40 |   inv i(x: Ref) {
             ^
  Type Error: invariant i implements interface M's abstract i, but its definition depends on N.test, which M also declares.
  [1]
