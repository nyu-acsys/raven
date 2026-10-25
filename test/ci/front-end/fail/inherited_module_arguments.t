  $ dune exec -- raven --shh --typeonly ./inherited_module_arguments.rav
  [Error] File "./inherited_module_arguments.rav", line 11, columns 71-72:
  11 | func cannot_erase_module_argument(x: Impl.B.T) returns (r: Box[Int]) { x }
                                                                              ^
  Type Error: Expected an expression of type
    Box[Int]
  but found an expression of type
    Box[Spec.Element].
  [Error] File "./inherited_module_arguments.rav", line 12, columns 74-75:
  12 | func cannot_merge_inherited_modules(x: Impl.B.T) returns (r: Other.B.T) { x }
                                                                                 ^
  Type Error: Expected an expression of type
    Box[Spec.Element]
  but found an expression of type
    Box[Spec.Element].
  [1]
