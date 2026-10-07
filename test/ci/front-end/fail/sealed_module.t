  $ dune exec -- raven --shh ./sealed_module_representation.rav
  [Error] File "./sealed_module_representation.rav", line 44, columns 33-34:
  44 | lemma l() ensures Sealed.zero == 0 {}
                                        ^
  Type Error: Expected an expression of type
    Sealed.T
  but found an expression of type
    Int.
  [1]
  $ dune exec -- raven --shh ./sealed_module_hidden_member.rav
  [Error] File "./sealed_module_hidden_member.rav", line 44, columns 19-25:
  44 | lemma l() { Sealed.inside(); }
                          ^^^^^^
  Error: inside is not accessible here: Sealed is sealed with interface Counter and exposes only its members.
  [1]
  $ dune exec -- raven --shh ./sealed_module_view_type.rav
  [Error] File "./sealed_module_view_type.rav", line 44, columns 44-45:
  44 | lemma l(c: View.T) ensures IntCounter.value(c) == 0 {}
                                                   ^
  Type Error: Expected an expression of type
    Int
  but found an expression of type
    View.T.
  [1]
  $ dune exec -- raven --shh ./sealed_module_not_declared.rav
  [Error] File "./sealed_module_not_declared.rav", line 5, columns 7-8:
  5 | module M :> J = N
             ^
  Type Error: Module N does not declare that it implements interface J, so M cannot be sealed with it.
  [1]
  $ dune exec -- raven --shh ./sealed_module_no_definition.rav
  [Error] File "./sealed_module_no_definition.rav", line 4, columns 7-13:
  4 | module M :> J
             ^^^^^^
  Syntax Error: Module M has no definition, so it cannot be sealed with ':>'.
  [1]
