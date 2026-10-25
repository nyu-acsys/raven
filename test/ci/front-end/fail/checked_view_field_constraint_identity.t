  $ dune exec -- raven --shh ./checked_view_field_constraint_identity.rav
  [Error] File "./checked_view_field_constraint_identity.rav", line 5, columns 7-11:
  5 | module View : Required = checked Actual
             ^^^^
  Type Error: Checked module view: field constraints must agree.
  [1]
