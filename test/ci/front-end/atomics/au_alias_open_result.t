  $ raven --shh fail/au_alias_open_result.rav
  [Error] File "fail/au_alias_open_result.rav", line 8, columns 2-22:
  8 |   commitAU(first, ());
        ^^^^^^^^^^^^^^^^^^^^
  Verification Error: The token or arguments of commitAU may differ from the open atomic update.
  [Error] File "fail/au_alias_open_result.rav", line 7, columns 2-26:
  7 |   first := openAU(second);
        ^^^^^^^^^^^^^^^^^^^^^^^^
  Related Location: This atomic update was opened here.
  [1]
