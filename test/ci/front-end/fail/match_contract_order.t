  $ dune exec -- raven --shh --typeonly ./match_contract_order.rav
  [Error] File "./match_contract_order.rav", line 9, columns 7-13:
  9 |   proc select(choice: Choice) returns (r: Int)
             ^^^^^^
  Type Error: Procedure select does not have the same postcondition as select in interface Select. Repeat its contract exactly, or omit it to inherit it.
  [1]
