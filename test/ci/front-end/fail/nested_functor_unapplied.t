  $ dune exec -- raven --shh --typeonly ./nested_functor_unapplied.rav
  [Error] File "./nested_functor_unapplied.rav", line 8, columns 32-37:
  8 | module Bad = NeedsType[OuterInt.Inner]
                                      ^^^^^
  Type Error: Module OuterInt.Inner first needs to be instantiated to obtain a module with interface Library.Type.
  [1]
