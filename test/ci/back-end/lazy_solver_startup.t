Front-end runs do not launch Z3 or create its debug log.

  $ mkdir solver
  $ cat > solver/z3 <<'SCRIPT'
  > #!/bin/sh
  > touch solver-started
  > while IFS= read -r line; do
  >   case "$line" in
  >     '(check-sat)') printf '%s\n' unsat ;;
  >   esac
  > done
  > SCRIPT
  $ chmod +x solver/z3
  $ export PATH="$PWD/solver:$PATH"
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
