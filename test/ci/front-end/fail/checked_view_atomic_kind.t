  $ dune exec -- raven --shh ./checked_view_atomic_kind.rav
  [Error] File "./checked_view_atomic_kind.rav", line 7, columns 7-11:
  7 | module View : Required = checked Actual
             ^^^^
  Type Error: Checked module view: ordinary and logically atomic contract kinds differ.
  [1]
