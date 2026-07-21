  $ dune exec -- raven --shh ./mutual_incompatible_arity.rav
  [Error] File "./mutual_incompatible_arity.rav", line 10, columns 5-9:
  10 | proc pong(n: Int)
            ^^^^
  Type Error: this `decreases` clause has 1 measure component(s), but `ping` (in the same mutually-recursive group) has 2; every member of a mutually-recursive group must declare `decreases` clauses of the same arity.
  [1]
