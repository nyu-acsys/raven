  $ dune exec -- raven --shh ./inherit_duplicate_member.rav
  [Error] File "./inherit_duplicate_member.rav", line 8, columns 7-12:
  8 | module Clash : P1, P2 {
             ^^^^^
  Type Error: Member foo is declared by more than one of the interfaces Clash implements; a module cannot inherit two declarations of the same name.
  [1]
