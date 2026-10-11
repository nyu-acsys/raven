  $ python3 lsp_dependencies.py
  Dependencies are absolute, transitive and deduplicated across include cycles.
  Include paths follow --base-dir, including files outside the document directory.
  Missing includes are reported alongside diagnostics so their creation can be watched.
  Dependencies survive syntax errors in included files and update between checks.
