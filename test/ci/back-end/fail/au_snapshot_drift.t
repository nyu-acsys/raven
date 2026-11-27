  $ raven --shh au_snapshot_drift.rav
  [Error] File "au_snapshot_drift.rav", line 17, columns 2-31:
  17 |   commitAU(token, argument, 7);
         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: The token or arguments of commitAU may differ from the open atomic update.
  [Error] File "au_snapshot_drift.rav", line 15, columns 2-52:
  15 |   ghost var witness: Int := openAU(token, argument);
         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Related Location: This atomic update was opened here.
  [Error] File "au_snapshot_drift.rav", line 25, columns 2-30:
  25 |   commitAU(token, 7, witness);
         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: An atomic postcondition may not hold at this commit point.
  [Error] File "au_snapshot_drift.rav", line 25, columns 2-30:
  25 |   commitAU(token, 7, witness);
         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: A postcondition may not hold at this return point.
  [Error] File "au_snapshot_drift.rav", line 3, columns 17-34:
  3 |   atomic ensures result == witness
                       ^^^^^^^^^^^^^^^^^
  Related Location: This assertion may not hold.
  [Error] File "au_snapshot_drift.rav", line 32, columns 2-20:
  32 |   abortAU(token, 8);
         ^^^^^^^^^^^^^^^^^^
  Verification Error: The token or arguments of abortAU may differ from the open atomic update.
  [Error] File "au_snapshot_drift.rav", line 31, columns 2-45:
  31 |   ghost var witness: Int := openAU(token, 7);
         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Related Location: This atomic update was opened here.
  [Error] File "au_snapshot_drift.rav", line 41, columns 2-26:
  41 |   commitAU(current, 7, 7);
         ^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: The token or arguments of commitAU may differ from the open atomic update.
  [Error] File "au_snapshot_drift.rav", line 39, columns 2-47:
  39 |   ghost var witness: Int := openAU(current, 7);
         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Related Location: This atomic update was opened here.
  [Error] File "au_snapshot_drift.rav", line 52, columns 2-24:
  52 |   commitAU(right, 7, 7);
         ^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: The token or arguments of commitAU may differ from the open atomic update.
  [Error] File "au_snapshot_drift.rav", line 50, columns 4-46:
  50 |     ghost var second: Int := openAU(right, 7);
           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Related Location: This atomic update was opened here.
  [1]
