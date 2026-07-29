  $ dune exec -- raven --shh ./val_reassign_new.rav
  [Error] File "./val_reassign_new.rav", line 6, columns 2-3:
  6 |   y := new(f: 2);
        ^
  Type Error: Cannot assign to value y.
  [1]
