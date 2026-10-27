  $ dune exec -- raven --shh ./invariant_footprints_structural.rav
  [Error] File "./invariant_footprints_structural.rav", line 15, columns 7-15:
  15 | module Selected : Regions = checked Actual
              ^^^^^^^^
  Type Error: The implementations of distinct invariant regions Regions.first and Regions.second share invariant dependencies cell.
  [1]
