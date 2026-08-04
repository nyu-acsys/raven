  $ dune exec -- raven --shh ./commit_au_not_open.rav
  [Error] File "./commit_au_not_open.rav", line 16, columns 2-20:
  16 |   commitAU(phi, ());
         ^^^^^^^^^^^^^^^^^^
  Verification Error: Cannot commitAU: atomic token phi is not open.
  [1]
