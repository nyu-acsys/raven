  $ dune exec -- raven --shh ./ghost_block_read_destination.rav
  [Error] File "./ghost_block_read_destination.rav", line 7, columns 5-13:
  7 |   {! ordinary := x.integer; !}
           ^^^^^^^^
  Type Error: Cannot assign to non-ghost var ordinary in ghost context.
  [1]
