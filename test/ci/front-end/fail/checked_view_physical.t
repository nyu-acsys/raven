  $ dune exec -- raven --shh ./checked_view_physical.rav
  [Error] File "./checked_view_physical.rav", line 3, columns 7-11:
  3 | module View : Required = checked Actual
             ^^^^
  Type Error: Checked module view: an atomic proc requires a physically atomic actual procedure.
  [1]
