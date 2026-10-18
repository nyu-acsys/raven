The cache skips the obligations verified before. The stub solver verifies everything
by default, and with RAVEN_TEST_RESPONSE=sat refutes whatever it is asked to check, so a
run with it succeeds only if all obligations are found in the cache.

  $ mkdir solver
  $ cp ../unit/smt_stub.exe solver/z3
  $ cp ../unit/smt_stub.exe solver/z3.exe
  $ chmod +x solver/z3 solver/z3.exe
  $ export PATH="$PWD/solver:$PATH"
  $ dune exec -- raven --shh --cache-dir cache fingerprints.rav
  Verification successful.
  $ RAVEN_TEST_RESPONSE=sat dune exec -- raven --shh --cache-dir cache fingerprints.rav
  Verification successful.

After an edit of the callee's contract, the callee (lines 15-21) and its caller (lines
23-27) are checked again.

  $ sed 's/ensures own(x.f, double(n), 1.0)/& \&\& n >= 0/' fingerprints.rav > edited.rav
  $ RAVEN_TEST_RESPONSE=sat dune exec -- raven --shh --cache-dir cache edited.rav 2>&1 | grep '^\[Error\]'
  [Error] File "edited.rav", line 19, columns 2-15:
  [Error] File "edited.rav", line 20, columns 1-1:
  [Error] File "edited.rav", line 17, columns 10-34:
  [Error] File "edited.rav", line 17, columns 38-44:
  [Error] File "edited.rav", line 26, columns 2-15:
  [Error] File "edited.rav", line 16, columns 11-27:
  [Error] File "edited.rav", line 16, columns 31-37:
  [Error] File "edited.rav", line 27, columns 1-1:
  [Error] File "edited.rav", line 24, columns 27-43:
  [Error] File "edited.rav", line 24, columns 47-53:

A failure is not cached, so they are checked again on the next run, too.

  $ RAVEN_TEST_RESPONSE=sat dune exec -- raven --shh --cache-dir cache edited.rav 2>&1 | grep -c '^\[Error\]'
  10
  $ dune exec -- raven --shh --cache-dir cache edited.rav
  Verification successful.
  $ RAVEN_TEST_RESPONSE=sat dune exec -- raven --shh --cache-dir cache edited.rav
  Verification successful.

Without the directory, everything is checked.

  $ RAVEN_TEST_RESPONSE=sat dune exec -- raven --shh fingerprints.rav 2>&1 | grep -c '^\[Error\]'
  17
