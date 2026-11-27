  $ dune exec -- raven --shh ./defined_within_foreign.rav
  [Error] File "./defined_within_foreign.rav", line 9, columns 27-47:
  9 |   inv leaf(x: Int, k: Int) within Roots.root(x) { true }
                                 ^^^^^^^^^^^^^^^^^^^^
  Type Error: A within clause of an invariant with a definition must name an invariant in the same module.
  [1]
