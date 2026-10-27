  $ dune exec -- raven --shh --typeonly ./nested_inherited_datatypes.rav
  [Error] File "./nested_inherited_datatypes.rav", line 15, columns 7-8:
  15 | { r := x; }
              ^
  Type Error: Expected an expression of type
    Second.Data.T
  but found an expression of type
    First.Data.T.
  [1]
