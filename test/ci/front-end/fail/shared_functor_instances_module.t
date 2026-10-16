  $ dune exec -- raven --shh ./shared_functor_instances_module.rav
  [Error] File "./shared_functor_instances_module.rav", line 15, columns 21-22:
  15 |   assert GM.identity(s) == s;
                            ^
  Type Error: Expected an expression of type
    Library.Seq[MyInt]
  but found an expression of type
    Library.Seq[Int].
  [1]
