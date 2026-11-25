  $ dune exec -- raven --shh loop_masks.rav
  [Error] File "loop_masks.rav", line 21, columns 6-24:
  21 |       unfold counter(z);
             ^^^^^^^^^^^^^^^^^^
  Verification Error: Invariant counter is not in the current mask.
  [1]
