  $ dune exec -- raven --shh --typeonly ./inherited_sealed_module_argument.rav
  [Error] File "./inherited_sealed_module_argument.rav", line 19, columns 14-20:
  19 |     result := values;
                     ^^^^^^
  Type Error: Expected an expression of type
    Library.List[Argument.Element.Carrier]
  but found an expression of type
    Library.List[Int].
  [1]
