  $ dune exec -- raven --shh ./mask_implicit_parameter_grants.rav > failures.log 2>&1
  [1]
  $ rg -c 'Verification Error:' failures.log
  3
  $ rg -qi 'timeout' failures.log
  [1]
