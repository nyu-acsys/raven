  $ dune exec -- raven --shh ./inherit_shared_ancestor.rav
  [Error] File "./inherit_shared_ancestor.rav", line 10, columns 7-14:
  10 | module Diamond : L, R { }
              ^^^^^^^
  Type Error: Interfaces L and R cannot both be implemented here: they share the ancestor Root.
  [1]
