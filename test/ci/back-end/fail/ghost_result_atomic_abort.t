  $ dune exec -- raven --shh ./ghost_result_atomic_abort.rav
  [Error] File "./ghost_result_atomic_abort.rav", line 22, columns 2-32:
  22 |   ghost val previous := reset(c)
         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: An invariant open around this atomic call may not be closable if the call aborts.
  [Error] File "./ghost_result_atomic_abort.rav", line 20, columns 2-16:
  20 |   unfold cell(c)
         ^^^^^^^^^^^^^^
  Related Location: This invariant may not be closable again if the call aborts.
  [Error] File "./ghost_result_atomic_abort.rav", line 22, columns 2-32:
  22 |   ghost val previous := reset(c)
         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Related Location: This own predicate may not hold.
  [1]
