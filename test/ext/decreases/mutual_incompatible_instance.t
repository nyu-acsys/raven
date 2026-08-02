  $ dune exec -- raven --shh ./mutual_incompatible_instance.rav
  [Error] File "./mutual_incompatible_instance.rav", line 17, columns 5-9:
  17 | proc pong(n: Int)
            ^^^^
  Type Error: this `decreases` clause uses a different WellFoundedOrder instance than ping (in the same mutually-recursive group) at some lexicographic position; every member of a mutually-recursive group must use matching instances position-by-position.
  [1]
