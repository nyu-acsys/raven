  $ raven --shh fail/au_alias_reassign.rav
  [Error] File "fail/au_alias_reassign.rav", line 9, columns 2-23:
  9 |   commitAU(second, ());
        ^^^^^^^^^^^^^^^^^^^^^
  Verification Error: Cannot commitAU: atomic token second is not open.
  [1]
