  $ dune exec -- raven --shh ./abstract_invariant_reach_back.rav
  [Error] File "./abstract_invariant_reach_back.rav", line 35, columns 6-7:
  35 |   inv i(x: Ref) {
             ^
  Type Error: invariant i implements interface M's abstract i, but its definition depends on N.test, which M also declares.
  [1]
