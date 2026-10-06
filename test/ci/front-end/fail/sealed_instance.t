  $ dune exec -- raven --shh ./sealed_instance.rav
  [Error] File "./sealed_instance.rav", line 11, columns 7-13:
  11 | module M :> I = F[Library.IntType]
              ^^^^^^
  Syntax Error: Module M has no body, so it cannot be sealed with ':>'; seal the functor it instantiates instead.
  [1]
