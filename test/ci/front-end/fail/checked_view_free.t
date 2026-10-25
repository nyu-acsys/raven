  $ dune exec -- raven --shh ./checked_view_free.rav
  [Error] File "./checked_view_free.rav", line 3, columns 12-16:
  3 | free module View : Required = checked Actual
                  ^^^^
  Type Error: A checked module view must be a verified module binding.
  [1]
