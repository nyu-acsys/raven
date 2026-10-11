import json
from pathlib import Path
import subprocess

source = Path('lsp_inherited_opens.rav')
result = subprocess.run(
    ['dune', 'exec', '--', 'raven', '--shh', '-q', '--lsp-mode',
     '--lsp-annotations', '--typeonly', str(source)],
    text=True, encoding='utf-8', capture_output=True, check=True,
)
assert not result.stderr, result.stderr
output = json.loads(result.stdout)
assert output['errors'] == [], output
contracts = {
    item['source']: item['clauses']
    for item in output['annotations'] if item['kind'] == 'InheritedContract'
}
expected = {
    'J.empty': [('opens', '{}')],
    'J.touch': [('requires', 'cell(r)'), ('ensures', 'cell(r)'), ('opens', 'cell(r)')],
    'J.wildcards': [('opens', 'pair(r, _), cell(r)')],
    'J.swapped': [('opens', 'pair(y, x)')],
}
assert {
    name: [(clause['keyword'], clause['text']) for clause in clauses]
    for name, clauses in contracts.items()
} == expected, contracts
print('Inherited opens clauses preserve empty masks, wildcards and parameter renaming.')

lines = source.read_text(encoding='utf-8').splitlines()
for clauses in contracts.values():
    for clause in clauses:
        if clause['keyword'] != 'opens':
            continue
        assert Path(clause['file']).resolve() == source.resolve(), clause
        assert clause['start_line'] == clause['end_line'], clause
        line = lines[clause['start_line'] - 1]
        assert line[clause['start_col']:clause['end_col']] == line.strip(), clause
        assert line.strip().startswith('opens '), clause
print('Opens annotations point to the original clause through interface inheritance.')

modules = [item for item in output['annotations'] if item['kind'] == 'InheritedMembers']
assert len(modules) == 2, modules
assert len(modules[0]['members']) == 5, modules
for member in modules[0]['members']:
    assert '\n  opens ' in member['text'], member
assert modules[1]['members'][0]['text'] == 'lemma retained()\n  opens {} { … }', modules
print('Inherited-member hovers include trailing opens clauses and elide bodies.')
