  $ dune exec -- raven --shh --typeonly ./atomic_token_index_value.rav
  [Error] File "./atomic_token_index_value.rav", line 2, columns 22-41:
  2 | proc use(ghost token: AtomicToken<target>) { }
                            ^^^^^^^^^^^^^^^^^^^
  Type Error: Expected procedure with atomic specification.
  [1]

  $ dune exec -- raven --shh --typeonly ./atomic_token_index_function.rav
  [Error] File "./atomic_token_index_function.rav", line 2, columns 22-41:
  2 | proc use(ghost token: AtomicToken<target>) { }
                            ^^^^^^^^^^^^^^^^^^^
  Type Error: Expected procedure with atomic specification.
  [1]

  $ dune exec -- raven --shh --typeonly ./atomic_token_index_procedure.rav
  [Error] File "./atomic_token_index_procedure.rav", line 2, columns 22-41:
  2 | proc use(ghost token: AtomicToken<target>) { }
                            ^^^^^^^^^^^^^^^^^^^
  Type Error: Expected procedure with atomic specification.
  [1]

  $ dune exec -- raven --shh --typeonly ./atomic_token_index_physical.rav
  [Error] File "./atomic_token_index_physical.rav", line 2, columns 22-41:
  2 | proc use(ghost token: AtomicToken<target>) { }
                            ^^^^^^^^^^^^^^^^^^^
  Type Error: Expected procedure with atomic specification.
  [1]

  $ dune exec -- raven --shh --typeonly ./atomic_token_index_predicate.rav
  [Error] File "./atomic_token_index_predicate.rav", line 2, columns 22-41:
  2 | proc use(ghost token: AtomicToken<target>) { }
                            ^^^^^^^^^^^^^^^^^^^
  Type Error: Expected procedure with atomic specification.
  [1]

  $ dune exec -- raven --shh --typeonly ./atomic_token_index_invariant.rav
  [Error] File "./atomic_token_index_invariant.rav", line 2, columns 22-41:
  2 | proc use(ghost token: AtomicToken<target>) { }
                            ^^^^^^^^^^^^^^^^^^^
  Type Error: Expected procedure with atomic specification.
  [1]

  $ dune exec -- raven --shh --typeonly ./atomic_token_index_lemma.rav
  [Error] File "./atomic_token_index_lemma.rav", line 2, columns 22-41:
  2 | proc use(ghost token: AtomicToken<target>) { }
                            ^^^^^^^^^^^^^^^^^^^
  Type Error: Expected procedure with atomic specification.
  [1]

  $ dune exec -- raven --shh --typeonly ./atomic_token_index_bind.rav
  [Error] File "./atomic_token_index_bind.rav", line 1, columns 18-46:
  1 | proc ordinary() { ghost val token := bindAU(); }
                        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Type Error: Expected procedure with atomic specification.
  [1]
