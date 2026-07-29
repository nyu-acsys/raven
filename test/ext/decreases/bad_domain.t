  $ dune exec -- raven --shh ./bad_domain.rav
  [Error] File "./bad_domain.rav", line 2, columns 12-13:
  2 |   decreases b
                  ^
  Type Error: this decreases clause's measure type has no WellFoundedOrder instance.
  [1]
