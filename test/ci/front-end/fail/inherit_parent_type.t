  $ dune exec -- raven --shh ./inherit_parent_type.rav
  [Error] File "./inherit_parent_type.rav", line 3, columns 15-21:
  3 | module Child : Parent {}
                     ^^^^^^
  Type Error: Expected a module or interface in the parent clause, but found type Parent.
  [1]
