  $ dune exec -- raven --shh ./shared_functor_instances_module.rav
  [Error] File "./shared_functor_instances_module.rav", line 15, columns 21-22:
  15 |   assert GM.identity(s) == s;
                            ^
  Type Error: Expected an expression of type
    GenInst$$Library_Seq$$MyInt.T
  but found an expression of type
    GenInst$$Library_Seq$$TypeMod$$Library_Type$$Int.T.
  [1]
