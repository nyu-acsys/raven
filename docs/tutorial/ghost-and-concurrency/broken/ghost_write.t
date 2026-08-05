  $ dune exec -- raven --shh ./ghost_write.rav
  [Error] File "./ghost_write.rav", line 22, columns 6-11:
  22 |     c.count := 5
             ^^^^^
  Type Error: Cannot assign to non-ghost field count in ghost context.
  [1]
