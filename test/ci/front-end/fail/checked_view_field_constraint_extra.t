  $ dune exec -- raven --shh ./checked_view_field_constraint_extra.rav
  [Error] File "./checked_view_field_constraint_extra.rav", line 4, columns 7-11:
  4 | module View : Required = checked Actual
             ^^^^
  Type Error: Checked module view: field constraints must agree.
  [1]
