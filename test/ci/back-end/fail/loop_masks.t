  $ dune exec -- raven --shh loop_masks.rav
  [Error] File "loop_masks.rav", line 21, columns 6-24:
  21 |       unfold counter(z);
             ^^^^^^^^^^^^^^^^^^
  Verification Error: Cannot unfold counter: the available mask entry's arguments are not provably equal to this instance's.
  [1]
