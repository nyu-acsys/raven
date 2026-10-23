  $ dune exec -- raven --shh ./physical_atomic_proc_interface.rav
  [Error] File "./physical_atomic_proc_interface.rav", line 6, columns 7-8:
  6 |   proc f() { }
             ^
  Type Error: Procedure f implements an atomic proc declaration but is not atomic.
  [1]
