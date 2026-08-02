When the verifier is running inside a checkout it was built from, a library location
also carries `path`: the real file on disk, which an editor can open and edit rather
than serving a read-only copy. The path is only reported when that file is
byte-identical to the source embedded in the binary -- a checkout at a different
revision, or a library file edited since the build, is rejected rather than reported
with line numbers that no longer line up with what was verified.

The absolute path itself depends on where the tree lives, so this only checks that the
field is present and names the file the location is in.

  $ dune exec -- raven --lsp-mode -q ./lsp_library_loc.rav | grep -o '"path":"[^"]*"' | sed 's|"path":"[^"]*/\(lib/library/\)|"path":".../\1|' | sort -u
  "path":".../lib/library/resource_algebra.rav"

The reported path exists and its content is exactly what the binary would print for that
source, which is the invariant that makes the two interchangeable.

  $ dune exec -- raven --lsp-mode -q ./lsp_library_loc.rav | grep -o '"path":"[^"]*"' | head -1 | sed 's|"path":"\(.*\)"|\1|' > path.txt
  $ dune exec -- raven --shh --print-library-source lib/library/resource_algebra.rav | diff - "$(cat path.txt)" && echo identical
  identical
