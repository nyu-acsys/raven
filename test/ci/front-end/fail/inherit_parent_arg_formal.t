  $ dune exec -- raven --shh ./inherit_parent_arg_formal.rav
  [Error] File "./inherit_parent_arg_formal.rav", line 5, columns 34-35:
  5 | module Child[B: Unrelated] : Base[B] {}
                                        ^
  Type Error: Interface Child.B does not implement interface Required.
  [1]
