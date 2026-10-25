  $ dune exec -- raven --shh ./resource_alias_contract.rav
  [Error] File "./resource_alias_contract.rav", line 2, columns 18-22:
  2 | module Bad { pred cell(x: Ref) ensures true = cell }
                        ^^^^
  Type Error: A resource alias cannot declare contracts, locals or callable modifiers.
  [1]
