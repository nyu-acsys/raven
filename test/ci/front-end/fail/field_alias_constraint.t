  $ dune exec -- raven --shh ./field_alias_constraint.rav
  [Error] File "./field_alias_constraint.rav", line 4, columns 28-43:
  4 | module Wrong : Restricted { field f = value }
                                  ^^^^^^^^^^^^^^^
  Type Error: Field f has a different constraint from its interface.
  [1]
