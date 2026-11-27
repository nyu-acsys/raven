  $ dune exec -- raven --shh iterated_invariants.rav
  [Error] File "iterated_invariants.rav", line 11, columns 1-1:
  11 | }
        ^
  Verification Error: A postcondition may not hold at this return point.
  [Error] File "iterated_invariants.rav", line 9, columns 48-61:
  9 |   ensures forall j: Int :: 0 <= j && j <= n ==> tag(xs[j], j)
                                                      ^^^^^^^^^^^^^
  Related Location: This predicate may not hold.
  [1]
