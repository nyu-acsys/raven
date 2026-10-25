  $ dune exec -- raven --shh ./checked_view_manifest.rav
  [Error] File "./checked_view_manifest.rav", line 3, columns 7-11:
  3 | module View : Required = checked Actual
             ^^^^
  Type Error: Checked module view: manifest type does not match T.
  [1]
