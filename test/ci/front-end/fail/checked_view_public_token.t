  $ dune exec -- raven --shh ./checked_view_public_token.rav
  [Error] File "./checked_view_public_token.rav", line 18, columns 7-11:
  18 | module View : Required = checked Actual
              ^^^^
  Type Error: Checked module view: public atomic tokens require an explicit adapter.
  [1]
