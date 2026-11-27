  $ raven --shh fail/au_alias_reassign.rav
  [Error] File "fail/au_alias_reassign.rav", line 9, columns 2-23:
  9 |   commitAU(second, ());
        ^^^^^^^^^^^^^^^^^^^^^
  Verification Error: The token or arguments of commitAU may differ from the open atomic update.
  [Error] File "fail/au_alias_reassign.rav", line 7, columns 2-16:
  7 |   openAU(first);
        ^^^^^^^^^^^^^^
  Related Location: This atomic update was opened here.
  [1]
