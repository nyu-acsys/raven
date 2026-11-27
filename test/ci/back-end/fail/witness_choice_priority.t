A preferred witness must still satisfy every equality and ownership obligation.

  $ dune exec -- raven --shh ./witness_choice_priority.rav > failures.log 2>&1
  [1]
  $ grep -c 'Verification Error:' failures.log
  3
  $ grep -qi 'timeout' failures.log
  [1]
