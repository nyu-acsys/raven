  $ dune exec -- raven --shh ./mask_implicit_parameter_grants.rav > failures.log 2>&1
  [1]
  $ grep -c 'Verification Error:' failures.log
  3
  $ grep -qi 'timeout' failures.log
  [1]
