  $ dune exec -- raven --shh ./amortised_hash.rav
  [Error] File "./amortised_hash.rav", line 143, columns 6-31:
  143 |       EC.error(amortized_error)
              ^^^^^^^^^^^^^^^^^^^^^^^^^
  Error: this expression belongs to the eris extension; re-run with --extension eris.
  [Error] File "./amortised_hash.rav", line 228, columns 22-77:
  228 |     hashfun(x, mp) && EC.error(potential(max_hash_size, len(mp), val_size+1))
                              ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Error: this expression belongs to the eris extension; re-run with --extension eris.
  [Error] File "./amortised_hash.rav", line 276, columns 13-38:
  276 |     requires EC.error(amortized_error)
                     ^^^^^^^^^^^^^^^^^^^^^^^^^
  Error: this expression belongs to the eris extension; re-run with --extension eris.
  [Error] File "./amortised_hash.rav", line 286, columns 9-34:
  286 |       && EC.error(amortized_error)
                 ^^^^^^^^^^^^^^^^^^^^^^^^^
  Error: this expression belongs to the eris extension; re-run with --extension eris.
  [1]
