  $ dune exec -- raven --shh ./checked_view_precondition.rav
  [Error] File "./checked_view_precondition.rav", line 7, columns 7-11:
  7 | module View : Required = checked Actual
             ^^^^
  Verification Error: A precondition may not hold for this call.
  [Error] File "./checked_view_precondition.rav", line 5, columns 34-39:
  5 |   proc operation(x: Int) requires x > 0 { }
                                        ^^^^^
  Related Location: This assertion may not hold.
  [1]
