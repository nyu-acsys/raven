  $ dune exec -- raven --shh ./sealed_without_parameters.rav
  [Error] File "./sealed_without_parameters.rav", line 7, columns 7-8:
  7 | module M :> I {
             ^
  Type Error: Module M cannot be sealed with ':>' because it has no parameters; only functors can be sealed.
  [1]
