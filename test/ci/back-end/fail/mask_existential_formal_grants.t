  $ dune exec -- raven --shh ./mask_existential_formal_grants.rav 2>&1 | sed -n '/Verification Error:/p'
  Verification Error: Invariant cell is not in the current mask.
