  $ dune exec -- raven --shh ./assertion_labels_fail_assume.rav
  [Error] File "./assertion_labels_fail_assume.rav", line 3, columns 9-15:
  3 |   assume bounds: false;
               ^^^^^^
  Syntax Error: A name is only allowed in assert statements.
  [1]
