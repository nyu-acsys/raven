import assert from 'node:assert/strict'
import { spawnSync } from 'node:child_process'
import { cpSync, mkdirSync, mkdtempSync, readFileSync, readdirSync, rmSync, symlinkSync, writeFileSync } from 'node:fs'
import { createRequire } from 'node:module'
import { tmpdir } from 'node:os'
import { dirname, join } from 'node:path'
import { fileURLToPath } from 'node:url'
import test from 'node:test'

test('an installed package builds an independent site with its own palette and source languages', { timeout: 60000 }, t => {
  const root = mkdtempSync(join(tmpdir(), 'site-consumer-'))
  t.after(() => rmSync(root, { recursive: true, force: true }))
  const modules = join(root, 'node_modules')
  const installed = join(modules, '@nyu-acsys/docs-kit')
  const source = fileURLToPath(new URL('../', import.meta.url))
  mkdirSync(installed, { recursive: true })
  // Copy the package as an installation, rather than relying on a linked workspace.
  for (const file of ['src', 'bin', 'package.json']) cpSync(join(source, file), join(installed, file), { recursive: true })
  const require = createRequire(import.meta.url)
  const dependencies = dirname(dirname(require.resolve('vitepress/package.json')))
  try {
    for (const entry of readdirSync(dependencies)) {
      if (entry.startsWith('.') || entry === '@nyu-acsys') continue
      symlinkSync(join(dependencies, entry), join(modules, entry), process.platform === 'win32' ? 'junction' : 'dir')
    }
  } catch (error) {
    if (error.code === 'EPERM' || error.code === 'EACCES') return t.skip('Dependency links unavailable')
    throw error
  }
  const write = (file, text) => {
    mkdirSync(dirname(join(root, file)), { recursive: true })
    writeFileSync(join(root, file), text)
  }
  write('.vitepress/project.mjs', `
import { fileURLToPath } from 'node:url'
import { createSections } from '@nyu-acsys/docs-kit/sections'
const root = fileURLToPath(new URL('../', import.meta.url))
export default { root, pagesBase: '/caravan/', sourceExtensions: ['ml', 'mli', 'proof'], exampleSources: ['examples'],
  grammars: [{file: new URL('./proof.json', import.meta.url), aliases: ['proof']}],
  sections: createSections({root, chapters: [{path: 'guide/', label: '0'}], appendices: [{path: 'reference'}]}) }
`)
  write('.vitepress/config.mts', `
import { defineProjectSite } from '@nyu-acsys/docs-kit/config'
import project from './project.mjs'
export default defineProjectSite(project, {title: 'Independent site'})
`)
  write('.vitepress/theme/index.ts', "import Theme from '@nyu-acsys/docs-kit/theme'\nimport './palette.css'\nexport default Theme\n")
  write('.vitepress/theme/palette.css', ':root { --vp-c-brand-1: #996633; }\n')
  write('.vitepress/proof.json', JSON.stringify({name: 'Proof', scopeName: 'source.proof', patterns: [{match: 'lemma', name: 'keyword.control.proof'}]}))
  write('index.md', '# Independent site\n\nSee {{ref sec:first}} and {{ref app:reference}}.\n\n[Code](./examples/tiny.ml) [Signature](./examples/tiny.mli) [Proof](./examples/tiny.proof)\n\n```proof\nlemma keep\n```\n')
  write('guide/index.md', '# Guide\n\n## First {#sec:first}\n')
  write('reference.md', '# Reference\n\n## Terms {#sec:terms}\n')
  for (const extension of ['ml', 'mli', 'proof']) write(`examples/tiny.${extension}`, `example ${extension}\n`)
  const result = spawnSync(process.execPath, [join(installed, 'bin/project-docs.mjs'), 'build'], {
    cwd: root, env: { ...process.env, GITHUB_PAGES: 'true' }, encoding: 'utf8', timeout: 55000
  })
  assert.equal(result.status, 0, `${result.error ?? ''}\n${result.stdout}\n${result.stderr}`)
  const output = join(root, '.vitepress/dist')
  const html = readFileSync(join(output, 'index.html'), 'utf8')
  assert.ok(html.includes('/caravan/guide/#sec:first'))
  assert.ok(html.includes('/caravan/reference.html'))
  assert.equal(html.includes('/caravan/caravan/'), false)
  const links = [...html.matchAll(/href="([^"]+)"/g)].map(match => new URL(match[1], 'https://example.invalid/caravan/').pathname)
  for (const extension of ['ml', 'mli', 'proof']) {
    const name = `tiny.${extension}`
    assert.ok(links.includes(`/caravan/examples/${name}`))
    assert.equal(links.includes(`/caravan/examples/${name}.html`), false)
    assert.equal(readFileSync(join(output, 'examples', name), 'utf8'), `example ${extension}\n`)
  }
  assert.ok(readdirSync(join(output, 'assets')).some(file => file.endsWith('.css') && readFileSync(join(output, 'assets', file), 'utf8').includes('996633')))
  assert.ok(readFileSync(join(output, 'guide/index.html'), 'utf8').includes('class="section-number">0.1'))
  assert.ok(readFileSync(join(output, 'reference.html'), 'utf8').includes('Appendix A: Reference'))
})
