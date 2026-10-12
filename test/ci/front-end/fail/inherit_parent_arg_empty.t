  $ dune exec -- raven --shh ./inherit_parent_arg_empty.rav
  [Error] File "./inherit_parent_arg_empty.rav", line 7, columns 20-25:
  7 | module Child : Base[Wrong] {}
                          ^^^^^
  Type Error: Module Wrong does not implement interface Required.
  [1]
