  $ dune exec -- raven --shh ./box_underdetermined.rav
  [Error] File "./box_underdetermined.rav", line 26, columns 11-22:
  26 |   var n := Box.mkTag()
                  ^^^^^^^^^^^
  Type Error: Cannot infer a type argument for parameter T of Box; write an explicit instantiation, e.g. `module M_X = Box[...]`.
  [1]
