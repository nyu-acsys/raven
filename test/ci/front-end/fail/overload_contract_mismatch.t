  $ dune exec -- raven --shh ./overload_contract_mismatch.rav
  [Error] File "./overload_contract_mismatch.rav", line 9, columns 7-8:
  9 |   func f(c: Bool) returns (r: Bool)
             ^
  Type Error: Function f does not have the same postcondition as f in interface I. Repeat its contract exactly, or omit it to inherit it.
  [1]
