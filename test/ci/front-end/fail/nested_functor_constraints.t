  $ dune exec -- raven --shh --typeonly ./nested_functor_constraints.rav
  [Error] File "./nested_functor_constraints.rav", line 23, columns 41-56:
  23 | module WrongOperations = Selected.Worker[OtherOperations, Layout]
                                                ^^^^^^^^^^^^^^^
  Type Error: Module OtherOperations does not implement interface World[Int].Operations.
  [Error] File "./nested_functor_constraints.rav", line 24, columns 49-60:
  24 | module WrongLayout = Selected.Worker[Operations, OtherLayout]
                                                        ^^^^^^^^^^^
  Type Error: Module OtherLayout does not implement interface World[Int].Shape.
  [1]
