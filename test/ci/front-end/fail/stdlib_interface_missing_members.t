  $ dune exec -- raven --shh ./stdlib_interface_missing_members.rav
  [Error] File "./stdlib_interface_missing_members.rav", line 8, columns 7-8:
  8 | module M : Library.ResourceAlgebra {
             ^
  Type Error: Module M must be declared as an interface. The value id is still abstract.
  [1]
