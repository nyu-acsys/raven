  $ dune exec -- raven --shh match_stmt_missing.rav
  [Error] File "match_stmt_missing.rav", line 6, columns 19-52:
  6 | proc f(s: Shape) { match s { case circle(r) => { } } }
                         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Type Error: non-exhaustive match: missing case(s) for rect.
  [1]
  $ dune exec -- raven --shh match_stmt_arity.rav
  [Error] File "match_stmt_arity.rav", line 6, columns 19-78:
  6 | proc f(s: Shape) { match s { case circle(r, q) => { } case rect(w, h) => { } } }
                         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Type Error: 'circle' expects 1 pattern variable(s), but this arm binds 2.
  [1]
  $ dune exec -- raven --shh match_stmt_unknown.rav
  [Error] File "match_stmt_unknown.rav", line 6, columns 19-66:
  6 | proc f(s: Shape) { match s { case square(r) => { } case _ => { } } }
                         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Type Error: 'square' is not a constructor of this data type.
  [1]
  $ dune exec -- raven --shh match_stmt_wildcard_vars.rav
  [Error] File "match_stmt_wildcard_vars.rav", line 6, columns 19-69:
  6 | proc f(s: Shape) { match s { case circle(r) => { } case _(x) => { } } }
                         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Type Error: a wildcard ('_') match arm cannot bind pattern variables.
  [1]
  $ dune exec -- raven --shh match_stmt_not_data.rav
  [Error] File "match_stmt_not_data.rav", line 6, columns 17-42:
  6 | proc f(x: Int) { match x { case _ => { } } }
                       ^^^^^^^^^^^^^^^^^^^^^^^^^
  Type Error: a `match` scrutinee must have a `data` type.
  [1]
  $ dune exec -- raven --shh match_stmt_ghost.rav
  [Error] File "match_stmt_ghost.rav", line 6, columns 48-49:
  6 | proc f(ghost s: Shape) returns (x: Int) { match s { case circle(r) => { x := r; } case _ => { x := 0; } } }
                                                      ^
  Type Error: This expression reads ghost state, so it can only be used inside a ghost block, spec, or ghost-typed field.
  [1]
