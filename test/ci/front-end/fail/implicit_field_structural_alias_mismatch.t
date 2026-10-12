  $ dune exec -- raven --shh ./implicit_field_structural_alias_mismatch.rav
  [Error] File "./implicit_field_structural_alias_mismatch.rav", line 13, columns 20-36:
  13 |     var bad: Ref := Ops.key(x.table);
                           ^^^^^^^^^^^^^^^^
  Type Error: Cannot unify type Int with type Bool.
  [1]
