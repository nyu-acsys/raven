A related location inside the standard library is flagged `library` and named by its
path within the Raven repository, because there is no such file in the user's project to
resolve it against. An editor turns that into a read-only virtual document served by
`--print-library-source`.

The `path` field is dropped below: it appears only when the verifier is running inside a
checkout whose copy of the file matches the embedded one byte for byte, and it is an
absolute path, so it depends on where the tree happens to live. See lsp_library_path.t.

  $ dune exec -- raven --lsp-mode -q ./lsp_library_loc.rav | sed 's|,"path":"[^"]*"||g; s|},{|}\n{|g'
  [{"file":"lib/library/resource_algebra.rav","start_line":16,"start_col":13,"end_line":16,"end_col":24,"kind":"RelatedLoc","message":["Lemma compCommute inherited from axiom Library.ResourceAlgebra.compCommute"],"library":true}
  {"file":"./lsp_library_loc.rav","start_line":4,"start_col":10,"end_line":4,"end_col":10,"kind":"Verification","message":["A postcondition may not hold at this return point"]}
  {"file":"./lsp_library_loc.rav","start_line":4,"start_col":10,"end_line":4,"end_col":10,"kind":"Verification","message":["A postcondition may not hold at this return point"]}
  {"file":"lib/library/resource_algebra.rav","start_line":17,"start_col":55,"end_line":17,"end_col":79,"kind":"RelatedLoc","message":["This assertion may not hold"],"library":true}]

Locations in the file being checked are not flagged, so a client never mistakes an
ordinary path for a library one.

  $ dune exec -- raven --lsp-mode -q ./lsp_library_loc.rav | grep -c '"file":"\./[^"]*"[^}]*"library":true'
  0
  [1]
