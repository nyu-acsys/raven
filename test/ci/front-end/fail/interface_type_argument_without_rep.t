  $ dune exec -- raven --shh ./interface_type_argument_without_rep.rav
  [Error] File "./interface_type_argument_without_rep.rav", line 10, columns 28-31:
  10 | module IntWrapper : Wrapper[Int] {
                                   ^^^
  Type Error: Cannot pass a type as argument for parameter C: interface Counter does not declare a rep type.
  [1]
