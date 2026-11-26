  $ dune exec -- raven --shh ./cycle.rav
  [Error] File "./cycle.rav", line 1, columns 4-5:
  1 | inv a(x: Int) within b(x) { true }
          ^
  Type Error: Cyclic namespace ancestry.
  [1]
