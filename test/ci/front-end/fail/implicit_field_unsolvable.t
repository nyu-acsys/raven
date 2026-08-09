  $ dune exec -- raven --shh ./implicit_field_unsolvable.rav
  [Error] File "./implicit_field_unsolvable.rav", line 22, columns 32-50:
  22 |   proc use() returns (m: Int) { m := unrelated(3); }
                                       ^^^^^^^^^^^^^^^^^^
  Type Error: Cannot infer a field argument for parameter A of Ops, since this call takes no location; write an explicit instantiation, e.g. `module M_X = Ops[...]`.
  [1]
