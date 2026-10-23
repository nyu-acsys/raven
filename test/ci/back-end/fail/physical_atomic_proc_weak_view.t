  $ dune exec -- raven --shh ./physical_atomic_proc_weak_view.rav
  [Error] File "./physical_atomic_proc_weak_view.rav", line 16, columns 2-12:
  16 |   Strong.f()
         ^^^^^^^^^^
  Verification Error: Cannot take a non-atomic step while an invariant or atomic update is open.
  [1]
