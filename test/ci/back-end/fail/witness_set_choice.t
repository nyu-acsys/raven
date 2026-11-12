  $ dune exec -- raven --shh ./witness_set_choice.rav > failures.log 2>&1
  [1]
  $ rg -c 'Verification Error:' failures.log
  6
  $ rg -qi 'timeout' failures.log
  [1]
