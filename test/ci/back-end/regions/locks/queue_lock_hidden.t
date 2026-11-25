  $ dune exec -- raven --shh ./queue_lock_hidden.rav
  [Error] File "./queue_lock_hidden.rav", line 7, columns 13-23:
  7 |   unfold CLH.queued_loc(l, null, c);
                   ^^^^^^^^^^
  Error: queued_loc is not accessible here: CLH is an instance of the sealed module CLHLock, which exposes only the members of interface QueueLock.
  [Error] File "./queue_lock_hidden.rav", line 11, columns 13-28:
  11 |   unfold MCS.waiting_loc_inv(l, null, c);
                    ^^^^^^^^^^^^^^^
  Error: waiting_loc_inv is not accessible here: MCS is an instance of the sealed module MCSLock, which exposes only the members of interface QueueLock.
  [1]
