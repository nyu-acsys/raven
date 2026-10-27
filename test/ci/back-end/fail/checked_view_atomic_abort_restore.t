  $ dune exec -- raven --shh ./checked_view_atomic_abort_restore.rav
  [Error] File "./checked_view_atomic_abort_restore.rav", line 29, columns 7-11:
  29 | module View : Required = checked Actual
              ^^^^
  Verification Error: A precondition may not hold for this call where the atomic update or invariant open around it was opened, which is where it is given up.
  [Error] File "./checked_view_atomic_abort_restore.rav", line 29, columns 7-11:
  29 | module View : Required = checked Actual
              ^^^^
  Related Location: It was opened here.
  [Error] File "./checked_view_atomic_abort_restore.rav", line 7, columns 13-32:
  7 |     requires own(x.held, 0, 1.0)
                   ^^^^^^^^^^^^^^^^^^^
  Related Location: This own predicate may not hold.
  [1]
