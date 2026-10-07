  $ dune exec -- raven --shh ./inherited_contract_violated.rav
  [Error] File "./inherited_contract_violated.rav", line 18, columns 7-11:
  18 |   proc next(c: T) returns (r: T)
              ^^^^
  Related Location: Contract inherited from procedure Counter.next.
  [Error] File "./inherited_contract_violated.rav", line 31, columns 44-44:
  31 |   proc next(x: T) returns (z: T) { z := x; }
                                                   ^
  Verification Error: A postcondition may not hold at this return point.
  [Error] File "./inherited_contract_violated.rav", line 20, columns 12-36:
  20 |     ensures value(r) == value(c) + 1
                   ^^^^^^^^^^^^^^^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]
