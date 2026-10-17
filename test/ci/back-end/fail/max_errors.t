Every failed assertion is reported:

  $ dune exec -- raven --shh ./max_errors.rav
  [Error] File "./max_errors.rav", line 3, columns 9-14:
  3 |   assert x > 0;
               ^^^^^
  Verification Error: This assertion may be violated.
  [Error] File "./max_errors.rav", line 4, columns 9-14:
  4 |   assert x > 1;
               ^^^^^
  Verification Error: This assertion may be violated.
  [Error] File "./max_errors.rav", line 8, columns 9-14:
  8 |   assert x > 2;
               ^^^^^
  Verification Error: This assertion may be violated.
  [1]

With --max-errors, checking stops once there are more errors than the limit:

  $ dune exec -- raven --shh --max-errors=2 ./max_errors.rav
  [Error] File "./max_errors.rav", line 3, columns 9-14:
  3 |   assert x > 0;
               ^^^^^
  Verification Error: This assertion may be violated.
  [Error] File "./max_errors.rav", line 4, columns 9-14:
  4 |   assert x > 1;
               ^^^^^
  Verification Error: This assertion may be violated.
  [Error] Error: Stopped after 2 errors; use --max-errors to change the limit
  [1]

With --lsp-mode, there is no limit unless --max-errors is given:

  $ dune exec -- raven --shh --lsp-mode ./max_errors.rav
  [{"file":"./max_errors.rav","start_line":3,"start_col":9,"end_line":3,"end_col":14,"kind":"Verification","message":["This assertion may be violated"]},{"file":"./max_errors.rav","start_line":4,"start_col":9,"end_line":4,"end_col":14,"kind":"Verification","message":["This assertion may be violated"]},{"file":"./max_errors.rav","start_line":8,"start_col":9,"end_line":8,"end_col":14,"kind":"Verification","message":["This assertion may be violated"]}]
  $ dune exec -- raven --shh --lsp-mode --max-errors=2 ./max_errors.rav
  [{"file":"./max_errors.rav","start_line":3,"start_col":9,"end_line":3,"end_col":14,"kind":"Verification","message":["This assertion may be violated"]},{"file":"./max_errors.rav","start_line":4,"start_col":9,"end_line":4,"end_col":14,"kind":"Verification","message":["This assertion may be violated"]},{"file":"","start_line":0,"start_col":-1,"end_line":0,"end_col":-1,"kind":"Generic","message":["Stopped after 2 errors; use --max-errors to change the limit"]}]
