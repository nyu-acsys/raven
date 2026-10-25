  $ dune exec -- raven --shh ./checked_view_postcondition.rav
  [Error] File "./checked_view_postcondition.rav", line 2, columns 7-16:
  2 |   proc operation() returns (r: Int) ensures r > 0
             ^^^^^^^^^
  Related Location: Contract inherited from procedure Required.operation.
  [Error] File "./checked_view_postcondition.rav", line 7, columns 11-11:
  7 | module View : Required = checked Actual
                 ^
  Verification Error: A postcondition may not hold at this return point.
  [Error] File "./checked_view_postcondition.rav", line 2, columns 44-49:
  2 |   proc operation() returns (r: Int) ensures r > 0
                                                  ^^^^^
  Related Location: This assertion may not hold.
  [1]
