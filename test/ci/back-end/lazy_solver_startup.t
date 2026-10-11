Front-end runs do not launch Z3 or create its debug log.

  $ mkdir solver
  $ cp ../unit/smt_stub.exe solver/z3
  $ cp ../unit/smt_stub.exe solver/z3.exe
  $ chmod +x solver/z3 solver/z3.exe
  $ export PATH="$PWD/solver:$PATH"
  $ export RAVEN_TEST_STARTED=solver-started
  $ dune exec -- raven --shh --typeonly --verbosity=debug ./lazy_solver_startup.rav > /dev/null 2>&1
  $ test ! -e solver-started && test ! -e log.smt2
  $ dune exec -- raven --shh --stats --verbosity=debug ./lazy_solver_startup.rav > /dev/null 2>&1
  $ test ! -e solver-started && test ! -e log.smt2

Parse and type errors are reported before solver startup, including verification runs.

  $ echo 'lemma broken(' > malformed.rav
  $ dune exec -- raven --shh --verbosity=debug ./malformed.rav > /dev/null 2>&1
  [1]
  $ test ! -e solver-started && test ! -e log.smt2
  $ echo 'lemma broken() { assert 1; }' > ill_typed.rav
  $ dune exec -- raven --shh --verbosity=debug ./ill_typed.rav > /dev/null 2>&1
  [1]
  $ test ! -e solver-started && test ! -e log.smt2

Verification still starts a solver and writes its debug log.

  $ dune exec -- raven --shh --verbosity=debug ./lazy_solver_startup.rav > /dev/null 2>&1
  $ test -e solver-started && test -s log.smt2
