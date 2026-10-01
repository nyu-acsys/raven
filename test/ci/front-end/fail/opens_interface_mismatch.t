  $ dune exec -- raven --shh ./opens_interface_mismatch.rav
  [Error] File "./opens_interface_mismatch.rav", line 19, columns 8-13:
  19 |   lemma touch(x: Ref)
               ^^^^^
  Type Error: lemma touch does not have the same opens clause as touch in interface I.
  [1]
