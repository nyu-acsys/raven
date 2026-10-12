  $ dune exec -- raven --shh ./bind_duplicate_destination.rav
  [Error] File "./bind_duplicate_destination.rav", line 3, columns 5-6:
  3 |   x, x :| true;
           ^
  Type Error: Duplicate bind destination x.
  [1]
