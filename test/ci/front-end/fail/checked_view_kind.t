  $ dune exec -- raven --shh ./checked_view_kind.rav
  [Error] File "./checked_view_kind.rav", line 3, columns 7-11:
  3 | module View : Required = checked Actual
             ^^^^
  Type Error: Checked module view: no compatible member resource.
  [1]
