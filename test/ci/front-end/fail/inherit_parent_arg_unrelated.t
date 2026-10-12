  $ dune exec -- raven --shh ./inherit_parent_arg_unrelated.rav
  [Error] File "./inherit_parent_arg_unrelated.rav", line 9, columns 20-25:
  9 | module Child : Base[Wrong] {}
                          ^^^^^
  Type Error: Module Wrong does not implement interface Required.
  [1]
