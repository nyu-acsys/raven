  $ dune exec -- raven --shh ./inherit_parent_arg_dependent.rav
  [Error] File "./inherit_parent_arg_dependent.rav", line 13, columns 27-32:
  13 | module Child : Base[First, Wrong] {}
                                  ^^^^^
  Type Error: Module Wrong does not implement interface First.Required.
  [1]
