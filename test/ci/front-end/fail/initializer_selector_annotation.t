  $ dune exec -- raven --shh ./initializer_selector_annotation.rav
  [Error] File "./initializer_selector_annotation.rav", line 7, columns 2-29:
  7 |   var value: Bool := n.value;
        ^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Type Error: Expected an expression of type
    Bool
  but found an expression of type
    Int.
  [1]
