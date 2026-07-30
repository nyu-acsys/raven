  $ dune exec -- raven --shh ./lemma_writes_nonghost_field.rav
  [Error] File "./lemma_writes_nonghost_field.rav", line 7, columns 6-11:
  7 |     c.count := 6;
            ^^^^^
  Type Error: Cannot assign to non-ghost field count in ghost context.
  [1]
