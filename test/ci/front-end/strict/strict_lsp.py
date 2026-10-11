import json
import subprocess


def check(file, *flags):
    result = subprocess.run(
        ['dune', 'exec', '--', 'raven', '--lsp-mode', '-q', *flags, './' + file],
        text=True, capture_output=True, check=True,
    )
    assert not result.stderr, result.stderr
    return json.loads(result.stdout) if result.stdout.strip() else []


warnings = check('strict_lsp.rav', '--strict')
assert len(warnings) == 3, warnings
assert all(w['kind'] == 'Warning' and w['file'] == './strict_lsp.rav' for w in warnings)
assert [w['start_line'] for w in warnings] == [1, 3, 10], warnings
assert all(w['end_line'] >= w['start_line'] and w['end_col'] > w['start_col'] for w in warnings)
assert 'free' in warnings[0]['message'][0]
assert 'decreases' in warnings[1]['message'][0]
assert 'atomic' in warnings[2]['message'][0]
print('Strict warnings have source locations and survive quiet mode.')

annotated = check('strict_lsp.rav', '--strict', '--lsp-annotations')
assert annotated['errors'] == warnings
assert isinstance(annotated['annotations'], list)
print('Both LSP output formats contain the same warnings.')

assert check('strict_lsp.rav') == []
assert len(check('strict_lsp.rav', '--strict', '--typeonly')) == 1
print('Warnings are opt-in; type-only checking still reports explicit free declarations.')

mixed = check('strict_lsp_failure.rav', '--strict')
assert [w['kind'] for w in mixed] == ['Warning', 'Verification'], mixed
print('Warnings are preserved alongside verification errors.')

included = check('free_via_include.rav', '--strict')
assert len(included) == 1 and included[0]['kind'] == 'Warning', included
assert included[0]['file'] == './free_via_include.rav' and included[0]['start_line'] == 1
assert 'free_included_lib.rav' in included[0]['message'][0]
print('Included-file warnings are anchored at the include and retain their origin.')
