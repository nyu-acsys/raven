  $ dune exec -- raven --shh --nostdlib base_types.rav resource_algebra.rav
  Verification successful.

A library file that declares a field cannot be checked with --nostdlib: the
resource algebra and type wrapper generated for a field are named relative to
Library, which is exactly what --nostdlib leaves out. So atomics.rav is checked
*against* the standard library rather than in place of it, as an ordinary
program. That its own copy in the library is trusted -- the whole library is
machine-free, so its bodies are never re-verified in a user's program -- is what
makes covering it here worth doing.

  $ dune exec -- raven --shh ./atomics.rav
  Verification successful.

Checked as an ordinary program rather than imported, its bodies are intact and
genuinely reverified, so `--strict` warns about its four `atomic { ... }` blocks
exactly as it would for any other input -- the four primitives are library code,
not privileged, and take on the same trust obligation any hand-written one does.
When the same file is instead loaded as the standard library (the ordinary case,
every other test in this repo), those bodies are stripped before type-checking
and the warnings cannot occur at all; see test/ci/front-end/strict/atomic_block_library.rav.

  $ dune exec -- raven --shh --strict ./atomics.rav
  [Warning] File "./atomics.rav", line 63, column 4 to line 76, column 5:
  63 |     atomic {
           ^^^^^^^^
  this `atomic` block's body is assumed to be a single machine step, not checked; Raven has no model of the target machine to verify that against
  [Warning] File "./atomics.rav", line 87, column 4 to line 100, column 5:
  87 |     atomic {
           ^^^^^^^^
  this `atomic` block's body is assumed to be a single machine step, not checked; Raven has no model of the target machine to verify that against
  [Warning] File "./atomics.rav", line 109, column 4 to line 117, column 5:
  109 |     atomic {
            ^^^^^^^^
  this `atomic` block's body is assumed to be a single machine step, not checked; Raven has no model of the target machine to verify that against
  [Warning] File "./atomics.rav", line 133, column 4 to line 141, column 5:
  133 |     atomic {
            ^^^^^^^^
  this `atomic` block's body is assumed to be a single machine step, not checked; Raven has no model of the target machine to verify that against
  Verification successful.
