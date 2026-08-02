  $ dune exec -- raven --shh --strict ./mixed_coverage.rav
  [Error] File "./mixed_coverage.rav", line 10, columns 5-15:
  10 | proc no_measure(n: Int)
            ^^^^^^^^^^
  Type Error: no_measure does not declare a `decreases` clause, but it is mutually recursive with has_measure, which declare(s) one; every member of a mutually-recursive group must declare a `decreases` clause, or none of them may -- otherwise this cycle's termination isn't actually guaranteed by the check.
  [1]
