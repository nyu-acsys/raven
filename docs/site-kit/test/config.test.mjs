import assert from 'node:assert/strict'
import { mkdtempSync, mkdirSync, rmSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join } from 'node:path'
import test from 'node:test'
import { defineProjectSite, existingBasePage, siteBase, sourceExtensions } from '../src/config.mjs'

test('project bases support local previews and independent Pages sites', () => {
  for (const name of ['raven', 'caravan']) {
    const project = { pagesBase: `/${name}/` }
    assert.equal(siteBase(project, false), '/')
    assert.equal(siteBase(project, true), `/${name}/`)
  }
  for (const pagesBase of ['caravan/', '/caravan', '//caravan/', '/../', '/x?y/', '/x\\y/']) {
    assert.throws(() => siteBase({ pagesBase }, true), /Pages base/)
  }
})

test('source extensions are explicit and reusable for OCaml proof files', () => {
  assert.deepEqual(sourceExtensions({}), [])
  assert.deepEqual(sourceExtensions({ sourceExtensions: ['ml', 'mli', 'proof', 'ml'] }), ['ml', 'mli', 'proof'])
  for (const extension of ['.ml', 'ml,rav', '../proof']) {
    assert.throws(() => sourceExtensions({ sourceExtensions: [extension] }), /Source extensions/)
  }
})

test('base-path workaround accepts existing pages and keeps genuine dead links', t => {
  const root = mkdtempSync(join(tmpdir(), 'site-config-'))
  t.after(() => rmSync(root, { recursive: true, force: true }))
  mkdirSync(join(root, 'guide'))
  writeFileSync(join(root, 'guide/index.md'), '# Guide')
  writeFileSync(join(root, 'reference.md'), '# Reference')
  assert.ok(existingBasePage(root, '/caravan/', '/caravan/guide/index#intro'))
  assert.ok(existingBasePage(root, '/caravan/', '/caravan/guide/'))
  assert.ok(existingBasePage(root, '/caravan/', '/caravan/reference.html'))
  assert.equal(existingBasePage(root, '/caravan/', '/caravan/missing'), false)
  assert.equal(existingBasePage(root, '/caravan/', '/raven/reference'), false)
  assert.equal(existingBasePage(root, '/caravan/', '/caravan/../reference'), false)
  assert.equal(existingBasePage(root, '/', '/reference'), false)
})

test('sites retain their own metadata, grammars and palette configuration', t => {
  const root = mkdtempSync(join(tmpdir(), 'site-config-'))
  t.after(() => rmSync(root, { recursive: true, force: true }))
  writeFileSync(join(root, 'proof.json'), JSON.stringify({ name: 'Proof', scopeName: 'source.proof', patterns: [] }))
  const installed = []
  const config = defineProjectSite({ root, pagesBase: '/caravan/', sourceExtensions: ['ml', 'mli', 'proof'],
    grammars: [{ file: 'proof.json', aliases: ['caravan-proof'] }],
    sections: { install(md) { installed.push(['sections', md]) } }
  }, { title: 'Caravan', themeConfig: { logo: '/camel.png', nav: [{ text: 'Start', link: '/start/' }] },
    srcExclude: ['examples/internal/**'],
    markdown: { config(md) { installed.push(['custom', md]) } } })
  assert.equal(config.title, 'Caravan')
  assert.equal(config.themeConfig.logo, '/camel.png')
  assert.ok(config.vite.ssr.noExternal.includes('@nyu-acsys/docs-kit'))
  assert.equal(config.markdown.languages[0].scopeName, 'source.proof')
  assert.deepEqual(config.markdown.languages[0].aliases, ['caravan-proof'])
  assert.ok(config.srcExclude.includes('examples/internal/**'))
  const renderer = {}
  config.markdown.config(renderer)
  assert.deepEqual(installed, [['sections', renderer], ['custom', renderer]])
  assert.ok(config.ignoreDeadLinks[0].test('/guide/example.proof'))
  assert.equal(config.ignoreDeadLinks[0].test('/guide/missing.html'), false)
})
