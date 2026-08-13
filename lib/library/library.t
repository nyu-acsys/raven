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
