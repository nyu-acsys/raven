  $ dune exec -- raven --shh --typeonly ./depends_twice.rav
  [Error] File "./depends_twice.rav", line 2, columns 28-38:
  2 |   pred p(x: Ref) depends {} depends {}
                                  ^^^^^^^^^^
  Syntax Error: A callable may have at most one depends clause.
  [1]
