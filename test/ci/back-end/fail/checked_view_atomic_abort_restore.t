  $ dune exec -- raven --shh ./checked_view_atomic_abort_restore.rav
  [Error] File "./checked_view_atomic_abort_restore.rav", line 29, columns 7-11:
  29 | module View : Required = checked Actual
              ^^^^
  Verification Error: The atomic update open around this atomic call may not be abortable if the call aborts.
  [Error] File "./checked_view_atomic_abort_restore.rav", line 29, columns 7-11:
  29 | module View : Required = checked Actual
              ^^^^
  Related Location: This atomic update may not be abortable if the call aborts.
  [Error] File "./checked_view_atomic_abort_restore.rav", line 25, columns 20-39:
  25 |     atomic requires own(x.held, 0, 1.0) && own(x.count, n, 1.0)
                           ^^^^^^^^^^^^^^^^^^^
  Related Location: This own predicate may not hold.
  [1]
