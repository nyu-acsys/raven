  $ raven --shh fail/au_alias_branch.rav
  [Error] File "fail/au_alias_branch.rav", line 13, columns 2-23:
  13 |   commitAU(second, ());
         ^^^^^^^^^^^^^^^^^^^^^
  Verification Error: The token or arguments of commitAU may differ from the open atomic update.
  [Error] File "fail/au_alias_branch.rav", line 12, columns 2-16:
  12 |   openAU(first);
         ^^^^^^^^^^^^^^
  Related Location: This atomic update was opened here.
  [1]
