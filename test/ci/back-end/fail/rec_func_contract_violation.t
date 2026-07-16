  $ dune exec -- raven --shh ./rec_func_contract_violation.rav
  [Error] File "./rec_func_contract_violation.rav", line 4, columns 8-8:
  4 | func sum(n: Int) returns (res: Int)
              ^
  Verification Error: The postcondition of sum may not hold.
  [Error] File "./rec_func_contract_violation.rav", line 5, columns 10-18:
  5 |   ensures res >= n
                ^^^^^^^^
  Related Location: This assertion may not hold.
  [1]
