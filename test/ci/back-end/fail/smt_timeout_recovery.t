A query that gets no answer in time times out, and checking goes on with a new solver.

  $ mkdir solver
  $ cp ../../unit/smt_stub.exe solver/z3
  $ cp ../../unit/smt_stub.exe solver/z3.exe
  $ chmod +x solver/z3 solver/z3.exe
  $ PATH="$PWD/solver:$PATH" RAVEN_TEST_HANG=hung RAVEN_TEST_RESPONSE=sat dune exec -- raven --shh --nostdlib --smt-timeout=500 ./smt_timeout_recovery.rav
  [Error] File "./smt_timeout_recovery.rav", line 2, columns 16-20:
  2 |   assert first: true;
                      ^^^^
  Verification Error: Assertion 'first': This assertion may be violated. The solver timed out (see --smt-timeout).
  [Error] File "./smt_timeout_recovery.rav", line 6, columns 17-21:
  6 |   assert second: true;
                       ^^^^
  Verification Error: Assertion 'second': This assertion may be violated.
  [1]
