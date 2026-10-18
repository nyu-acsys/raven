With --counterexamples, a failed check shows the values of the variables, and the fields
of the references among them, where it fails. Whether the solver decides a check or gives
up on it can differ between versions, which only changes "Counterexample" to "Possible
counterexample", so the two are shown alike here.

  $ dune exec -- raven --shh --counterexamples ./counterexample.rav 2>&1 | sed 's/Possible counterexample/Counterexample/'
  [Error] File "./counterexample.rav", line 12, columns 9-15:
  12 |   assert z == 6;
                ^^^^^^
  Verification Error: This assertion may be violated.
  [Error] Counterexample:
    r = ref#1
    s = ref#1
    v = 3
    x = 3
    y = 6
    z = 7
    r.f = 4 (permission 1)
    s.f = 4 (permission 1)
  [Error] File "./counterexample.rav", line 22, columns 20-26:
  22 |     invariant step: i == 0
                           ^^^^^^
  Verification Error: Assertion 'step': This loop invariant may not be maintained.
  [Error] File "./counterexample.rav", line 22, columns 20-26:
  22 |     invariant step: i == 0
                           ^^^^^^
  Related Location: This assertion may not hold.
  [Error] Counterexample:
    i = 1
    n = 2

Without the flag, there are none.

  $ dune exec -- raven --shh ./counterexample.rav 2>&1 | grep -c "ounterexample:" || true
  0
