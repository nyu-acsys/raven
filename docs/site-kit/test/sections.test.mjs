import assert from 'node:assert/strict'
import { mkdtempSync, mkdirSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { dirname, join } from 'node:path'
import test from 'node:test'
import { createMarkdownRenderer, disposeMdItInstance } from 'vitepress'
import { createSections, sectionItems } from '../src/sections.mjs'

function fixture(t) {
  const root = mkdtempSync(join(tmpdir(), 'site-sections-'))
  t.after(() => rmSync(root, { recursive: true, force: true }))
  const write = (path, content) => {
    const file = join(root, path)
    mkdirSync(dirname(file), { recursive: true })
    writeFileSync(file, content)
  }
  return { root, write }
}

test('numbered directories, standalone pages and appendix labels share one registry', t => {
  const { root, write } = fixture(t)
  write('guide/start/index.md', '# Start\n\n## First {#sec:first}\n\n## Unnumbered\n\n### Detail\n\n## Next {#sec:next}\n')
  write('guide/concurrent.md', '# Concurrency\n\n## Shared {#sec:shared}\n')
  write('reference/types.md', '# Types\n\n## Carrier {#sec:carrier}\n')
  write('reference/tools/index.md', '# Tools\n\n## Editor {#sec:editor}\n')
  const sections = createSections({ root,
    chapters: [{ path: 'guide/start/', label: '0' }, { path: 'guide/concurrent.md', label: '5.2' }],
    appendices: [{ path: 'reference/types' }, { path: 'reference/tools/', id: 'editor-tools' }]
  })
  const registry = sections.buildRegistry()
  assert.deepEqual(registry.sections['sec:first'], {
    number: '0.1', title: 'First', path: '/guide/start/', anchor: 'sec:first'
  })
  assert.equal(registry.sections['sec:next'].number, '0.2')
  assert.equal(registry.sections['sec:shared'].number, '5.2.1')
  assert.equal(registry.sections['sec:carrier'].number, 'A.1')
  assert.equal(registry.sections['sec:editor'].number, 'B.1')
  assert.deepEqual(registry.pagesOrder['/guide/start/'], ['sec:first', 'sec:next'])
  assert.deepEqual(sectionItems(registry, '/guide/start/', { 'sec:first': 'First', 'sec:next': 'Next' }), [
    { text: '0.1. First', link: '/guide/start/#sec:first' },
    { text: '0.2. Next', link: '/guide/start/#sec:next' }
  ])
  assert.throws(() => sectionItems(registry, '/guide/start/', {}), /Missing sidebar label/)
  assert.deepEqual(registry.pages['app:types'], {
    label: 'A', path: '/reference/types.html', file: 'reference/types.md'
  })
  assert.deepEqual(registry.pages['app:editor-tools'], {
    label: 'B', path: '/reference/tools/', file: 'reference/tools/index.md'
  })
})

test('appendix IDs remain symbolic when the configured order changes', t => {
  const { root, write } = fixture(t)
  write('sets.md', '# Sets\n\n## Union {#sec:union}\n')
  write('maps.md', '# Maps\n\n## Lookup {#sec:lookup}\n')
  const before = createSections({ root, appendices: [{ path: 'sets' }, { path: 'maps' }] }).buildRegistry()
  const after = createSections({ root, appendices: [{ path: 'maps' }, { path: 'sets' }] }).buildRegistry()
  assert.equal(before.pages['app:sets'].label, 'A')
  assert.equal(after.pages['app:sets'].label, 'B')
  assert.equal(after.sections['sec:union'].number, 'B.1')
  assert.equal(before.pages['app:sets'].path, after.pages['app:sets'].path)
})

test('ambiguous identities and missing configured pages fail explicitly', t => {
  const { root, write } = fixture(t)
  write('first.md', '# First\n\n## Same {#sec:duplicate}\n')
  write('second.md', '# Second\n\n## Same {#sec:duplicate}\n')
  assert.throws(() => createSections({ root,
    chapters: [{ path: 'first', label: '1' }, { path: 'first.md', label: '2' }]
  }), /Duplicate numbered page first/)
  assert.throws(() => createSections({ root,
    chapters: [{ path: 'guide/', label: '1' }, { path: 'guide/index.md', label: '2' }]
  }), /Duplicate numbered page guide\//)
  assert.throws(() => createSections({ root,
    appendices: [{ path: 'one/types' }, { path: 'two/types' }]
  }), /Duplicate appendix id app:types/)
  assert.throws(() => createSections({ root,
    chapters: [{ path: 'first', label: '1' }, { path: 'second', label: '2' }]
  }).buildRegistry(), /Duplicate section id sec:duplicate/)
  assert.throws(() => createSections({ root,
    chapters: [{ path: 'missing/', label: '1' }]
  }).buildRegistry(), /Cannot read numbered page missing\/index.md/)
  assert.throws(() => createSections({ root,
    chapters: [{ path: '../outside', label: '1' }]
  }), /must stay inside the site/)
})

test('sites without numbered pages do not scan unrelated content', t => {
  const { root, write } = fixture(t)
  write('index.md', '# Home\n')
  write('draft.md', '## Duplicate {#sec:duplicate}\n\n## Duplicate {#sec:duplicate}\n')
  assert.deepEqual(createSections({ root }).buildRegistry(), {
    sections: {}, pagesOrder: {}, pages: {}
  })
  write('index.md', '# Home\n\n## Start {#sec:start}\n')
  const registry = createSections({ root,
    chapters: [{ path: 'index.md', label: '1' }]
  }).buildRegistry()
  assert.equal(registry.sections['sec:start'].path, '/')
})

test('rendered numbering and references respect the deployment base', async t => {
  const { root, write } = fixture(t)
  const text = '# Start\n\n## First {#sec:first}\n\nSee {{ref sec:first}} and {{ref app:types}}.\n'
  write('guide/index.md', text)
  write('types.md', '# Types\n\n## Carrier {#sec:carrier}\n')
  const sections = createSections({ root,
    chapters: [{ path: 'guide/', label: '1' }], appendices: [{ path: 'types' }]
  })
  disposeMdItInstance()
  t.after(disposeMdItInstance)
  const md = await createMarkdownRenderer(root, {
    highlight: code => code, config: md => sections.install(md)
  }, '/caravan/')
  const rendered = md.render(text, { relativePath: 'guide/index.md' })
  assert.match(rendered, /id="sec:first"/)
  assert.match(rendered, /<span class="section-number">1\.1<\/span> First/)
  assert.match(rendered, /href="\/caravan\/guide\/#sec:first">§1\.1<\/a>/)
  assert.match(rendered, /href="\/caravan\/types\.html">Appendix A<\/a>/)
  const appendix = md.render(readFileSync(join(root, 'types.md'), 'utf-8'), { relativePath: 'types.md' })
  assert.match(appendix, /Appendix A: Types/)
  assert.match(appendix, /<span class="section-number">A\.1<\/span> Carrier/)
  assert.throws(() => md.render('{{ref sec:missing}}', { relativePath: 'guide/index.md' }), /does not match any numbered section/)
  assert.throws(() => md.render('{{ref app:missing}}', { relativePath: 'guide/index.md' }), /does not match any appendix/)
  assert.match(md.render('`{{ref sec:missing}}`', {}), /<code>\{\{ref sec:missing\}\}<\/code>/)
})

test('development renders refresh references even when the render environment is reused', async t => {
  const { root, write } = fixture(t)
  write('other.md', '# Other\n\n## Existing {#sec:existing}\n')
  const sections = createSections({ root, chapters: [{ path: 'other', label: '2' }] })
  disposeMdItInstance()
  t.after(disposeMdItInstance)
  const md = await createMarkdownRenderer(root, {
    highlight: code => code, config: md => sections.install(md)
  })
  const env = { relativePath: 'index.md' }
  assert.match(md.render('See {{ref sec:existing}}.', env), />§2\.1<\/a>/)
  write('other.md', '# Other\n\n## Inserted {#sec:new}\n\n## Existing {#sec:existing}\n')
  assert.match(md.render('See {{ref sec:existing}}.', env), />§2\.2<\/a>/)
})

test('numbered pages cannot resolve outside the configured site', t => {
  const { root } = fixture(t)
  const outside = mkdtempSync(join(tmpdir(), 'outside-sections-'))
  t.after(() => rmSync(outside, { recursive: true, force: true }))
  writeFileSync(join(outside, 'page.md'), '## Outside {#sec:outside}\n')
  try {
    symlinkSync(outside, join(root, 'linked'), process.platform === 'win32' ? 'junction' : 'dir')
  } catch (error) {
    if (error.code === 'EPERM' || error.code === 'EACCES') return t.skip('Symlinks unavailable')
    throw error
  }
  assert.throws(() => createSections({ root,
    chapters: [{ path: 'linked/page', label: '1' }]
  }).buildRegistry(), /resolves outside the site/)
})
