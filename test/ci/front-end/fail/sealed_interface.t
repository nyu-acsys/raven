  $ dune exec -- raven --shh ./sealed_interface.rav
  [Error] File "./sealed_interface.rav", line 7, columns 10-11:
  7 | interface J[E: Library.Type] :> I {
                ^
  Type Error: Interface J cannot be sealed with ':>'.
  [1]
