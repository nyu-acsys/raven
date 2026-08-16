  $ dune exec -- raven --shh ./rdcss.rav
  [Warning] File "./rdcss.rav", line 627, columns 23-48:
  627 |       exists q1: Real, token: AtomicToken<rdcss> , tid_ghost_winner: Proph[Int] :: 
                               ^^^^^^^^^^^^^^^^^^^^^^^^^
  No witness could be computed for token -- it will be treated as an arbitrary unconstrained value, which may cause later assertions about it to fail.
  [Warning] File "./rdcss.rav", line 627, columns 51-79:
  627 |       exists q1: Real, token: AtomicToken<rdcss> , tid_ghost_winner: Proph[Int] :: 
                                                           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  No witness could be computed for tid_ghost_winner -- it will be treated as an arbitrary unconstrained value, which may cause later assertions about it to fail.
  Verification successful.
