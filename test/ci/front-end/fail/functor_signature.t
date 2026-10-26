  $ dune exec -- raven --shh --typeonly ./functor_signature_fixed.rav
  [Error] File "./functor_signature_fixed.rav", line 11, columns 25-30:
  11 | module Accepted = Client[Fixed]
                                ^^^^^
  Type Error: The functor does not preserve its interface's parameter-to-result mapping.
  [1]

  $ dune exec -- raven --shh --typeonly ./functor_signature_sealed_fixed.rav
  [Error] File "./functor_signature_sealed_fixed.rav", line 12, columns 25-31:
  12 | module Accepted = Client[Hidden]
                                ^^^^^^
  Type Error: The functor does not preserve its interface's parameter-to-result mapping.
  [1]

  $ dune exec -- raven --shh --typeonly ./functor_signature_permuted.rav
  [Error] File "./functor_signature_permuted.rav", line 8, columns 25-32:
  8 | module Rejected = Client[Swapped]
                               ^^^^^^^
  Type Error: The functor does not preserve its interface's parameter-to-result mapping.
  [1]

  $ dune exec -- raven --shh --typeonly ./functor_signature_constraints.rav
  [Error] File "./functor_signature_constraints.rav", line 9, columns 25-33:
  9 | module Rejected = Client[Stronger]
                               ^^^^^^^^
  Type Error: The functor has incompatible parameter constraints.
  [1]

  $ dune exec -- raven --shh --typeonly ./functor_signature_member_alias.rav
  [Error] File "./functor_signature_member_alias.rav", line 8, columns 37-41:
  8 | module Rejected : Container { module Make = Fixed }
                                           ^^^^
  Type Error: The functor does not preserve its interface's parameter-to-result mapping.
  [1]

  $ dune exec -- raven --shh --typeonly ./functor_signature_member_definition.rav
  [Error] File "./functor_signature_member_definition.rav", line 6, columns 9-13:
  6 |   module Make[X: Library.Type] : Signature[Int] {
               ^^^^
  Type Error: The functor does not preserve its interface's parameter-to-result mapping.
  [1]
