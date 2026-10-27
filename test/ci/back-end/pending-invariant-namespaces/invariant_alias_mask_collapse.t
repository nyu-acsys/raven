  $ dune exec -- raven --shh ./invariant_alias_mask_collapse.rav
  [Error] File "./invariant_alias_mask_collapse.rav", line 37, columns 7-14:
  37 | module Applied = Worker[Actual]
              ^^^^^^^
  Type Error: The implementations of distinct invariant regions Worker.P.first and Worker.P.second share invariant dependencies cell.
  [1]
