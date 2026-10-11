import json
from pathlib import Path
import subprocess
import tempfile


def check(root, file):
    result = subprocess.run(
        ['dune', 'exec', '--', 'raven', '-q', '--lsp-mode', '--lsp-annotations',
         '--typeonly', '--base-dir', str(root), str(file)],
        text=True, capture_output=True, check=True,
    )
    assert not result.stderr, result.stderr
    return json.loads(result.stdout)


with tempfile.TemporaryDirectory() as tmp:
    root = Path(tmp)
    includes = root / 'includes'
    includes.mkdir()
    middle = includes / 'middle.rav'
    leaf = includes / 'leaf.rav'
    middle.write_text('include "./leaf.rav"\ninclude "leaf.rav"\n')
    leaf.write_text('include "middle.rav"\n')
    source = root / 'editor-copy.rav'
    source.write_text('// include "ignored.rav"\ninclude "includes/middle.rav"\n')
    output = check(root, source)
    assert output['errors'] == [], output
    assert output['dependencies'] == sorted([middle.as_posix(), leaf.as_posix()]), output
    print('Dependencies are absolute, transitive and deduplicated across include cycles.')

    workspace = root / 'workspace'
    workspace.mkdir()
    source.write_text('include "../includes/middle.rav"\n')
    output = check(workspace, source)
    assert output['errors'] == [], output
    assert output['dependencies'] == sorted([middle.as_posix(), leaf.as_posix()]), output
    print('Include paths follow --base-dir, including files outside the document directory.')
    source.write_text('include "includes/middle.rav"\n')

    leaf.write_text('include "missing.rav"\n')
    output = check(root, source)
    missing = includes / 'missing.rav'
    assert output['errors'], output
    assert output['dependencies'] == sorted([
        middle.as_posix(), leaf.as_posix(), missing.as_posix()
    ]), output
    print('Missing includes are reported alongside diagnostics so their creation can be watched.')

    missing.write_text('')
    assert check(root, source)['errors'] == []
    leaf.write_text('module Broken {')
    output = check(root, source)
    assert output['errors'], output
    assert output['dependencies'] == sorted([middle.as_posix(), leaf.as_posix()]), output
    print('Dependencies survive syntax errors in included files and update between checks.')
