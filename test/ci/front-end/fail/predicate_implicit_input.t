  $ dune exec -- raven --shh ./predicate_implicit_input.rav
  [Error] File "./predicate_implicit_input.rav", line 1, columns 30-36:
  1 | pred p(x: Ref, implicit ghost n: Int) { true }
                                    ^^^^^^
  Type Error: Implicit predicate parameters must follow the ';' delimiter.
  [1]
