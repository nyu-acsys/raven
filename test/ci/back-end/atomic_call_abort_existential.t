An abort restores an existential atomic precondition with a fresh witness.

  $ raven --shh fail/atomic_call_abort_existential.rav
  [Error] File "fail/atomic_call_abort_existential.rav", line 27, columns 2-11:
  27 |   reset(x);
         ^^^^^^^^^
  Verification Error: An invariant open around this atomic call may not be closable if the call aborts.
  [Error] File "fail/atomic_call_abort_existential.rav", line 25, columns 2-17:
  25 |   unfold zero(x);
         ^^^^^^^^^^^^^^^
  Related Location: This invariant may not be closable again if the call aborts.
  [Error] File "fail/atomic_call_abort_existential.rav", line 27, columns 2-11:
  27 |   reset(x);
         ^^^^^^^^^
  Related Location: This own predicate may not hold.
  [1]
