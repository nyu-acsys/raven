Only an unsatisfiable negated assertion proves the original assertion.

  $ mkdir solver
  $ cat > solver/z3 <<'SCRIPT'
  > #!/bin/sh
  > while IFS= read -r line; do
  >   case "$line" in
  >     '(check-sat)') printf '%s\n' "$RAVEN_TEST_RESPONSE" ;;
  >     '(exit)') exit 0 ;;
  >   esac
  > done
  > SCRIPT
  $ chmod +x solver/z3
  $ PATH="$PWD/solver:$PATH" RAVEN_TEST_RESPONSE=unsat dune exec -- raven --shh --nostdlib ./smt_unknown.rav
  Verification successful.
  $ PATH="$PWD/solver:$PATH" RAVEN_TEST_RESPONSE=unknown dune exec -- raven --shh --nostdlib ./smt_unknown.rav
  [Error] File "./smt_unknown.rav", line 2, columns 16-20:
  2 |   assert known: true;
                      ^^^^
  Verification Error: Assertion 'known': This assertion may be violated.
  [1]
  $ PATH="$PWD/solver:$PATH" RAVEN_TEST_RESPONSE=sat dune exec -- raven --shh --nostdlib ./smt_unknown.rav
  [Error] File "./smt_unknown.rav", line 2, columns 16-20:
  2 |   assert known: true;
                      ^^^^
  Verification Error: Assertion 'known': This assertion may be violated.
  [1]
  $ PATH="$PWD/solver:$PATH" RAVEN_TEST_RESPONSE=unexpected dune exec -- raven --shh --nostdlib ./smt_unknown.rav
  [Error] Internal Error: Z3 returned unexpected output while checking this proof obligation: unexpected (re-run with --verbosity=debug to inspect log.smt2)
  [1]
