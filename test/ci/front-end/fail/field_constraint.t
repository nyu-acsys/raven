  $ dune exec -- raven --shh ./field_constraint_unknown.rav
  [Error] File "./field_constraint_unknown.rav", line 1, columns 19-23:
  1 | field f: Int where nope
                         ^^^^
  Error: Unknown identifier nope.
  [1]
  $ dune exec -- raven --shh ./field_constraint_signature.rav
  [Error] File "./field_constraint_signature.rav", line 3, columns 19-20:
  3 | field f: Int where g
                         ^
  Type Error: The constraint g of field f must be a func taking one Int and returning a Bool.
  [1]
  $ dune exec -- raven --shh ./field_constraint_ra.rav
  [Error] File "./field_constraint_ra.rav", line 5, columns 23-24:
  5 | ghost field f: A where g
                             ^
  Type Error: Field f has a resource algebra as its type, so it cannot have a constraint; build the constraint into the algebra's validity.
  [1]
