  $ dune exec -- raven --shh ./invariant_footprints_overlap.rav
  [Error] File "./invariant_footprints_overlap.rav", line 9, columns 7-13:
  9 | module Actual : Regions {
             ^^^^^^
  Type Error: The implementations of distinct invariant regions Regions.first and Regions.second share invariant dependencies cell.
  [1]
