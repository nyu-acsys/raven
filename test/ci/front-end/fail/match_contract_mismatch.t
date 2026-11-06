  $ dune exec -- raven --shh --typeonly ./match_contract_mismatch.rav
  [Error] File "./match_contract_mismatch.rav", line 7, columns 7-11:
  7 |   proc head(values: List[Int]) returns (result: Int)
             ^^^^
  Type Error: Procedure head does not have the same postcondition as head in interface ListHead. Repeat its contract exactly, or omit it to inherit it.
  [1]
