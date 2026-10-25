  $ dune exec -- raven --shh --typeonly ./applicative_contract_aliases.rav
  [Error] File "./applicative_contract_aliases.rav", line 16, columns 7-11:
  16 |   proc keep(x: Int)
              ^^^^
  Type Error: Procedure keep does not have the same precondition as keep in interface Client. Repeat its contract exactly, or omit it to inherit it.
  [1]
